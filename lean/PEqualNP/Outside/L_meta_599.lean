import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_599_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/-! ### Basic wire evaluation helpers -/

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma wiresFrom_nil (w : List Bool) : wiresFrom [] w = w := rfl

lemma wiresFrom_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wiresFrom (g :: gs) w =
      wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

lemma wiresFrom_append (gs₁ gs₂ : List Gate) (w : List Bool) :
    wiresFrom (gs₁ ++ gs₂) w = wiresFrom gs₂ (wiresFrom gs₁ w) := by
  induction gs₁ generalizing w with
  | nil => rfl
  | cons g gs ih => simp only [List.cons_append, wiresFrom_cons, ih]

lemma wiresFrom_length (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [wiresFrom]
  | cons g gs ih => rw [wiresFrom_cons, ih]; simp; omega

lemma getD_snoc_lt {α : Type*} (l : List α) (x d : α) {i : ℕ} (hi : i < l.length) :
    (l ++ [x]).getD i d = l.getD i d := by
  simp [List.getD, List.getElem?_append_left hi]

lemma getD_snoc_eq {α : Type*} (l : List α) (x d : α) :
    (l ++ [x]).getD l.length d = x := by
  simp [List.getD]

lemma wiresFrom_getD_lt (gs : List Gate) (w : List Bool) {i : ℕ} (hi : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [wiresFrom_cons, ih _ (by simp; omega)]
    exact getD_snoc_lt _ _ _ hi

lemma ofFn_getD_lt {α : Type*} {n : ℕ} (f : Fin n → α) (d : α) {i : ℕ} (hi : i < n) :
    (List.ofFn f).getD i d = f ⟨i, hi⟩ := by
  rw [List.getD_eq_getElem _ _ (by simp; exact hi), List.getElem_ofFn]

lemma wiresFrom_gate_getD (gs : List Gate) (w : List Bool) {j : ℕ} (hj : j < gs.length) :
    (wiresFrom gs w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i => (wiresFrom (gs.take j) w).getD i false) := by
  have hsplit : gs = gs.take j ++ gs[j] :: gs.drop (j + 1) := by simp
  conv_lhs => rw [hsplit, wiresFrom_append, wiresFrom_cons]
  set W := wiresFrom (gs.take j) w
  have hW : W.length = w.length + j := by
    rw [wiresFrom_length, List.length_take, Nat.min_eq_left hj.le]
  rw [wiresFrom_getD_lt _ _ (by simp [hW]), ← hW, getD_snoc_eq]

lemma wiresFrom_take_getD (gs : List Gate) (w : List Bool) {j i : ℕ}
    (hj : j < gs.length) (hi : i < w.length + j) :
    (wiresFrom (gs.take j) w).getD i false = (wiresFrom gs w).getD i false := by
  conv_rhs => rw [← List.take_append_drop j gs, wiresFrom_append]
  have hlen : (wiresFrom (gs.take j) w).length = w.length + j := by
    rw [wiresFrom_length, List.length_take, Nat.min_eq_left hj.le]
  exact (wiresFrom_getD_lt _ _ (by omega)).symm

lemma eval_mono_op (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (l₁ l₂ : List Bool) (hlen : l₁.length = l₂.length)
    (hle : ∀ k (hk : k < l₁.length), l₁[k] = true → l₂[k]'(by omega) = true) :
    op.eval l₁ = true → op.eval l₂ = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true, id_eq]
    intro h b hb
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hb
    exact hle k (by omega) (h l₁[k] (List.getElem_mem _))
  · simp only [GateOp.eval, List.any_eq_true, id_eq]
    rintro ⟨b, hb, rfl⟩
    obtain ⟨k, hk, hbk⟩ := List.getElem_of_mem hb
    exact ⟨l₂[k]'(by omega), List.getElem_mem _, hle k hk hbk⟩

lemma wiresFrom_mono (gs : List Gate)
    (hmono : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ (w₁ w₂ : List Bool), w₁.length = w₂.length →
      (∀ i, w₁.getD i false = true → w₂.getD i false = true) →
      ∀ i, (wiresFrom gs w₁).getD i false = true → (wiresFrom gs w₂).getD i false = true := by
  induction gs with
  | nil => intro w₁ w₂ _ hle i; exact hle i
  | cons g gs ih =>
    intro w₁ w₂ hlen hle i
    rw [wiresFrom_cons, wiresFrom_cons]
    have hstep : g.op.eval (g.inputs.map fun k => w₁.getD k false) = true →
        g.op.eval (g.inputs.map fun k => w₂.getD k false) = true := by
      apply eval_mono_op g.op (hmono g List.mem_cons_self) _ _ (by simp)
      intro k hk h1
      simp only [List.getElem_map] at h1 ⊢
      exact hle _ h1
    apply ih (fun g' hg' => hmono g' (List.mem_cons_of_mem _ hg')) _ _ (by simp [hlen])
    intro k
    by_cases hlt : k < w₁.length
    · rw [getD_snoc_lt _ _ _ hlt, getD_snoc_lt _ _ _ (by omega)]
      exact hle k
    · by_cases heq : k = w₁.length
      · subst heq
        rw [getD_snoc_eq, hlen, getD_snoc_eq]
        exact hstep
      · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
        exact id

lemma circuit_mono {n : ℕ} {C : Circuit} (hmono : Monotone2 C) {x y : Fin n → Bool}
    (hle : ∀ i, x i = true → y i = true) :
    C.eval (List.ofFn x) = true → C.eval (List.ofFn y) = true := by
  apply wiresFrom_mono C.gates (fun g hg => (hmono g hg).1) (List.ofFn x) (List.ofFn y) (by simp)
  intro i hi
  by_cases hlt : i < n
  · rw [ofFn_getD_lt _ _ hlt] at hi ⊢
    exact hle ⟨i, hlt⟩ hi
  · rw [List.getD_eq_default _ _ (by simp; omega)] at hi
    cases hi

/-! ### OR-gate counting and specification -/

def isOrOp : GateOp → Bool
  | GateOp.or => true
  | _ => false

lemma isOrOp_eq_true (op : GateOp) : isOrOp op = true ↔ op = GateOp.or := by
  cases op <;> simp [isOrOp]

lemma isOrOp_and : isOrOp GateOp.and = false := rfl
lemma isOrOp_or : isOrOp GateOp.or = true := rfl

def orCount (C : Circuit) : ℕ :=
  (C.gates.filter (fun g => isOrOp g.op)).length

lemma orCount_le_card {C : Circuit} {A : Finset ℕ}
    (hA : ∀ (j : ℕ) (g : Gate), C.gates[j]? = some g → g.op = GateOp.or → j ∈ A) :
    orCount C ≤ A.card := by
  let S : Finset ℕ := (Finset.range C.gates.length).filter
    (fun j => isOrOp (C.gates.getD j ⟨GateOp.and, []⟩).op = true)
  have hsub : S ⊆ A := by
    intro j hj
    simp only [S, Finset.mem_filter, Finset.mem_range] at hj
    rw [List.getD_eq_getElem _ _ hj.1, isOrOp_eq_true] at hj
    exact hA j C.gates[j] (List.getElem?_eq_getElem hj.1) hj.2
  have hcard : orCount C = S.card := by
    unfold orCount
    clear hA hsub
    suffices ∀ gs : List Gate, (gs.filter (fun g => isOrOp g.op)).length =
        ((Finset.range gs.length).filter (fun j => isOrOp (gs.getD j ⟨GateOp.and, []⟩).op = true)).card by
      exact this C.gates
    intro gs
    induction gs using List.reverseRecOn with
    | nil => simp
    | append_singleton gs g ih =>
      rw [List.filter_append, List.length_append, List.length_append, List.length_singleton,
          Finset.range_add_one, Finset.filter_insert]
      have hsub_eq : (Finset.range gs.length).filter
          (fun j => isOrOp ((gs ++ [g]).getD j ⟨GateOp.and, []⟩).op = true) =
          (Finset.range gs.length).filter
          (fun j => isOrOp (gs.getD j ⟨GateOp.and, []⟩).op = true) := by
        apply Finset.filter_congr
        intro j hj
        rw [Finset.mem_range] at hj
        rw [getD_snoc_lt _ _ _ hj]
      have hlast : (gs ++ [g]).getD gs.length ⟨GateOp.and, []⟩ = g := getD_snoc_eq gs g _
      rw [hlast, hsub_eq]
      cases hg : isOrOp g.op <;> simp [hg, ih, Finset.card_insert_of_notMem]
  rw [hcard]
  exact Finset.card_le_card hsub

def unitVec {n : ℕ} (u : Fin n) : Fin n → Bool := fun i => decide (i = u)

def pairVec {n : ℕ} (u v : Fin n) : Fin n → Bool := fun i => decide (i = u ∨ i = v)

def ComputesEdges {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit) : Prop :=
  (∀ u v : Fin n, G.Adj u v → C.eval (List.ofFn (pairVec u v)) = true) ∧
  (∀ u : Fin n, C.eval (List.ofFn (unitVec u)) = false) ∧
  (∀ u v : Fin n, ¬ G.Adj u v → C.eval (List.ofFn (pairVec u v)) = false)

lemma computesEdges_of_eval {n : ℕ} {G : SimpleGraph (Fin n)} {C : Circuit}
    (heval : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = true ↔
      ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) :
    ComputesEdges G C := by
  refine ⟨?_, ?_, ?_⟩
  · intro u v huv
    exact (heval (pairVec u v)).2 ⟨u, v, huv, by simp [pairVec], by simp [pairVec]⟩
  · intro u
    apply Bool.eq_false_iff.2
    intro h
    obtain ⟨a, b, hab, ha, hb⟩ := (heval (unitVec u)).1 h
    simp only [unitVec, decide_eq_true_eq] at ha hb
    subst ha hb
    exact G.irrefl hab
  · intro u v hnot
    apply Bool.eq_false_iff.2
    intro h
    obtain ⟨a, b, hab, ha, hb⟩ := (heval (pairVec u v)).1 h
    simp only [pairVec, decide_eq_true_eq] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact G.irrefl hab
    · exact hnot hab
    · exact hnot hab.symm
    · exact G.irrefl hab

/-! ### Monotone constant-false propagation `elimFalse` -/

def elimFStep (n : ℕ) (acc : List (Option ℕ) × List Gate) (g : Gate) :
    List (Option ℕ) × List Gate :=
  let ins := g.inputs.map fun i => acc.1.getD i none
  match g.op with
  | GateOp.and =>
    if ins.any Option.isNone then
      (acc.1 ++ [none], acc.2)
    else
      (acc.1 ++ [some (n + acc.2.length)], acc.2 ++ [⟨GateOp.and, ins.filterMap id⟩])
  | GateOp.or =>
    match ins.filterMap id with
    | [] => (acc.1 ++ [none], acc.2)
    | [w] => (acc.1 ++ [some w], acc.2)
    | ws => (acc.1 ++ [some (n + acc.2.length)], acc.2 ++ [⟨GateOp.or, ws⟩])
  | _ => (acc.1 ++ [none], acc.2)

def elimFPass (n : ℕ) (gs : List Gate) (acc : List (Option ℕ) × List Gate) :
    List (Option ℕ) × List Gate :=
  gs.foldl (elimFStep n) acc

def initFVar (n : ℕ) (v : Fin n) : List (Option ℕ) :=
  List.ofFn fun i : Fin n => if i = v then none else some i.val

lemma elimFPass_nil (n : ℕ) (acc : List (Option ℕ) × List Gate) :
    elimFPass n [] acc = acc := rfl

lemma elimFPass_cons (n : ℕ) (g : Gate) (gs : List Gate) (acc : List (Option ℕ) × List Gate) :
    elimFPass n (g :: gs) acc = elimFPass n gs (elimFStep n acc g) := rfl

lemma elimFPass_append (n : ℕ) (gs₁ gs₂ : List Gate) (acc : List (Option ℕ) × List Gate) :
    elimFPass n (gs₁ ++ gs₂) acc = elimFPass n gs₂ (elimFPass n gs₁ acc) := by
  induction gs₁ generalizing acc with
  | nil => rfl
  | cons g gs ih => simp only [List.cons_append, elimFPass_cons, ih]

lemma elimFPass_fst_len (n : ℕ) (gs : List Gate) (acc : List (Option ℕ) × List Gate) :
    (elimFPass n gs acc).1.length = acc.1.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp [elimFPass]
  | cons g gs ih =>
    rw [elimFPass_cons, ih, List.length_cons]
    have : (elimFStep n acc g).1.length = acc.1.length + 1 := by
      unfold elimFStep
      cases g.op <;> simp only []
      · split_ifs <;> simp
      · split <;> simp
      · simp
      · simp
      · simp
    omega

lemma elimFPass_getD_lt (n : ℕ) (gs : List Gate) (acc : List (Option ℕ) × List Gate)
    {k : ℕ} (hk : k < acc.1.length) :
    (elimFPass n gs acc).1.getD k none = acc.1.getD k none := by
  induction gs generalizing acc with
  | nil => rfl
  | cons g gs ih =>
    have hstep : (elimFStep n acc g).1.length = acc.1.length + 1 ∧
        (elimFStep n acc g).1.getD k none = acc.1.getD k none := by
      unfold elimFStep
      cases g.op <;> simp only []
      · split_ifs <;> exact ⟨by simp, getD_snoc_lt _ _ _ hk⟩
      · split <;> exact ⟨by simp, getD_snoc_lt _ _ _ hk⟩
      · exact ⟨by simp, getD_snoc_lt _ _ _ hk⟩
      · exact ⟨by simp, getD_snoc_lt _ _ _ hk⟩
      · exact ⟨by simp, getD_snoc_lt _ _ _ hk⟩
    rw [elimFPass_cons, ih _ (by rw [hstep.1]; omega), hstep.2]

lemma elimFStep_mono2 (n : ℕ) (acc : List (Option ℕ) × List Gate) (g : Gate)
    (hacc : ∀ g' ∈ acc.2, g'.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g'.inputs.length ≤ 2)
    (hg : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    ∀ g' ∈ (elimFStep n acc g).2, g'.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g'.inputs.length ≤ 2 := by
  intro g' hg'
  unfold elimFStep at hg'
  have hlen_fm : ∀ l : List (Option ℕ), (l.filterMap id).length ≤ l.length := by
    intro l; induction l with
    | nil => simp
    | cons a l ih =>
      cases a with
      | none => change (l.filterMap id).length ≤ l.length + 1; omega
      | some k => change (l.filterMap id).length + 1 ≤ l.length + 1; omega
  have hglen : g.inputs.length ≤ 2 := hg.2
  rcases hg.1 with hop | hop
  · rw [hop] at hg'
    dsimp only at hg'
    split_ifs at hg'
    · exact hacc g' hg'
    · rcases List.mem_append.1 hg' with h | h
      · exact hacc g' h
      · simp only [List.mem_singleton] at h; subst h
        refine ⟨by simp, ?_⟩
        have h1 := hlen_fm (g.inputs.map fun i => acc.1.getD i none)
        simp only [List.length_map] at h1
        dsimp only; omega
  · rw [hop] at hg'
    dsimp only at hg'
    cases hfm : (g.inputs.map fun i => acc.1.getD i none).filterMap id with
    | nil => rw [hfm] at hg'; exact hacc g' hg'
    | cons w1 rest =>
      cases rest with
      | nil => rw [hfm] at hg'; exact hacc g' hg'
      | cons w2 rest2 =>
        rw [hfm] at hg'
        rcases List.mem_append.1 hg' with h | h
        · exact hacc g' h
        · simp only [List.mem_singleton] at h; subst h
          refine ⟨by simp, ?_⟩
          have h1 := hlen_fm (g.inputs.map fun i => acc.1.getD i none)
          rw [hfm] at h1
          simp only [List.length_map] at h1
          dsimp only; omega

lemma elimFPass_mono2 (n : ℕ) (gs : List Gate) (acc : List (Option ℕ) × List Gate)
    (hacc : ∀ g' ∈ acc.2, g'.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g'.inputs.length ≤ 2)
    (hgs : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    ∀ g' ∈ (elimFPass n gs acc).2, g'.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g'.inputs.length ≤ 2 := by
  induction gs generalizing acc with
  | nil => exact hacc
  | cons g gs ih =>
    rw [elimFPass_cons]
    exact ih _ (elimFStep_mono2 n acc g hacc (hgs g List.mem_cons_self))
      (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg'))

def optVal (w : List Bool) : Option ℕ → Bool
  | none => false
  | some j => w.getD j false

def optValid (m : ℕ) : Option ℕ → Prop
  | none => True
  | some j => j < m

def ElimFInv (n : ℕ) (w_in w_old : List Bool) (acc : List (Option ℕ) × List Gate) : Prop :=
  w_in.length = n ∧
  acc.1.length = w_old.length ∧
  ∀ i : ℕ,
    optValid (n + acc.2.length) (acc.1.getD i none) ∧
    optVal (wiresFrom acc.2 w_in) (acc.1.getD i none) = w_old.getD i false

lemma filterMap_all_none_false {l : List (Option ℕ)} {w : List Bool}
    (hnone : l.any Option.isNone = true) :
    (l.map (optVal w)).all id = false := by
  rw [List.any_eq_true] at hnone
  obtain ⟨a, ha, his⟩ := hnone
  cases a with
  | none =>
    apply Bool.eq_false_iff.2
    intro hall
    rw [List.all_eq_true] at hall
    have h1 := hall false (List.mem_map.2 ⟨none, ha, rfl⟩)
    cases h1
  | some _ => simp at his

lemma filterMap_all_some {l : List (Option ℕ)} {w : List Bool}
    (hnone : l.any Option.isNone = false) :
    (l.filterMap id).map (fun j => w.getD j false) = l.map (optVal w) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    cases a with
    | none => simp at hnone
    | some j =>
      simp only [List.any_cons, Option.isNone_some, Bool.false_or] at hnone
      change w.getD j false :: (l.filterMap id).map (fun j => w.getD j false) = w.getD j false :: l.map (optVal w)
      rw [ih hnone]

lemma filterMap_any_or {l : List (Option ℕ)} {w : List Bool} :
    ((l.filterMap id).map (fun j => w.getD j false)).any id = (l.map (optVal w)).any id := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    cases a with
    | none =>
      change ((l.filterMap id).map (fun j => w.getD j false)).any id = (false || (l.map (optVal w)).any id)
      rw [Bool.false_or, ih]
    | some j =>
      change (w.getD j false || ((l.filterMap id).map (fun j => w.getD j false)).any id) =
        (w.getD j false || (l.map (optVal w)).any id)
      rw [ih]

lemma elimFInv_step (n : ℕ) (w_in w_old : List Bool) (acc : List (Option ℕ) × List Gate)
    (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or)
    (hinv : ElimFInv n w_in w_old acc) :
    ElimFInv n w_in (w_old ++ [g.op.eval (g.inputs.map fun i => w_old.getD i false)])
      (elimFStep n acc g) := by
  obtain ⟨hwin, hlen, hi⟩ := hinv
  set W := wiresFrom acc.2 w_in with hW
  have hWlen : W.length = n + acc.2.length := by rw [hW, wiresFrom_length, hwin]
  set ins := g.inputs.map fun i => acc.1.getD i none with hins
  have hins_val : g.inputs.map (fun i => w_old.getD i false) = ins.map (optVal W) := by
    rw [hins, List.map_map]
    apply List.map_congr_left
    intro i _; exact (hi i).2.symm
  have hins_valid : ∀ j ∈ ins.filterMap id, j < n + acc.2.length := by
    intro j hj
    rw [List.mem_filterMap] at hj
    obtain ⟨o, ho, hoid⟩ := hj
    cases o with
    | none => cases hoid
    | some k =>
      injection hoid with hkj; subst hkj
      obtain ⟨idx, _, hidx⟩ := List.mem_map.1 ho
      have hv := (hi idx).1
      rw [hidx] at hv
      exact hv
  have hpres : ∀ (st_new : Option ℕ) (g_opt : List Gate),
      optValid (n + (acc.2 ++ g_opt).length) st_new →
      optVal (wiresFrom (acc.2 ++ g_opt) w_in) st_new = g.op.eval (ins.map (optVal W)) →
      ElimFInv n w_in (w_old ++ [g.op.eval (g.inputs.map fun i => w_old.getD i false)])
        (acc.1 ++ [st_new], acc.2 ++ g_opt) := by
    intro st_new g_opt hval_new hev_new
    refine ⟨hwin, by simp [hlen], ?_⟩
    intro i
    by_cases hieq : i = acc.1.length
    · subst hieq
      rw [getD_snoc_eq, hlen, getD_snoc_eq, hins_val]
      exact ⟨hval_new, hev_new⟩
    · have hne_old : i ≠ w_old.length := by omega
      have h1 : (acc.1 ++ [st_new]).getD i none = acc.1.getD i none := by
        by_cases hlt : i < acc.1.length
        · exact getD_snoc_lt _ _ _ hlt
        · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]
      have h2 : (w_old ++ [g.op.eval (g.inputs.map fun i => w_old.getD i false)]).getD i false =
          w_old.getD i false := by
        by_cases hlt : i < w_old.length
        · exact getD_snoc_lt _ _ _ hlt
        · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]
      rw [h1, h2]
      have ⟨hvi, hevi⟩ := hi i
      cases hst : acc.1.getD i none with
      | none => rw [hst] at hevi; exact ⟨trivial, hevi⟩
      | some k =>
        rw [hst] at hvi hevi
        simp only [optValid, List.length_append] at hvi ⊢
        refine ⟨by omega, ?_⟩
        simp only [optVal, wiresFrom_append, ← hW] at hevi ⊢
        rw [wiresFrom_getD_lt _ _ (by omega)]
        exact hevi
  unfold elimFStep
  rcases hg with hop | hop
  · rw [hop]; dsimp only
    by_cases hany : ins.any Option.isNone = true
    · simp only [← hins, hany, ↓reduceIte]
      have := hpres none [] trivial (by
        rw [hop]; simp only [List.append_nil, optVal, GateOp.eval]
        exact (filterMap_all_none_false hany).symm)
      simpa [hop] using this
    · have hanyf : ins.any Option.isNone = false := Bool.eq_false_iff.2 hany
      simp only [← hins, hanyf, Bool.false_eq_true, ↓reduceIte]
      have := hpres (some (n + acc.2.length)) [⟨GateOp.and, ins.filterMap id⟩]
        (by simp [optValid]) (by
          rw [hop]; simp only [optVal, wiresFrom_append, wiresFrom_cons, wiresFrom_nil, ← hW, ← hWlen, getD_snoc_eq, GateOp.eval]
          rw [filterMap_all_some hanyf])
      simpa [hop] using this
  · rw [hop]; dsimp only
    simp only [← hins]
    cases hfm : ins.filterMap id with
    | nil =>
      have := hpres none [] trivial (by
        rw [hop]; simp only [List.append_nil, optVal, GateOp.eval]
        have := filterMap_any_or (l := ins) (w := W)
        rw [hfm] at this; simpa using this)
      simpa [hop] using this
    | cons w1 rest =>
      cases rest with
      | nil =>
        have hw1 : w1 < n + acc.2.length := hins_valid w1 (by rw [hfm]; simp)
        have := hpres (some w1) [] (by simpa [optValid] using hw1) (by
          rw [hop]; simp only [List.append_nil, optVal, GateOp.eval, ← hW]
          have := filterMap_any_or (l := ins) (w := W)
          rw [hfm] at this; simpa using this)
        simpa [hop] using this
      | cons w2 rest2 =>
        have := hpres (some (n + acc.2.length)) [⟨GateOp.or, w1 :: w2 :: rest2⟩]
          (by simp [optValid]) (by
            rw [hop]; simp only [optVal, wiresFrom_append, wiresFrom_cons, wiresFrom_nil, ← hW, ← hWlen, getD_snoc_eq, GateOp.eval]
            have := filterMap_any_or (l := ins) (w := W)
            rw [hfm] at this; exact this)
        simpa [hop] using this

lemma elimFInv_pass (n : ℕ) (w_in : List Bool) (gs : List Gate) (w_old : List Bool)
    (acc : List (Option ℕ) × List Gate)
    (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (hinv : ElimFInv n w_in w_old acc) :
    ElimFInv n w_in (wiresFrom gs w_old) (elimFPass n gs acc) := by
  induction gs generalizing w_old acc with
  | nil => exact hinv
  | cons g gs ih =>
    rw [wiresFrom_cons, elimFPass_cons]
    exact ih _ _ (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg'))
      (elimFInv_step n w_in w_old acc g (hgs g List.mem_cons_self) hinv)

lemma elimFInv_initFVar (n : ℕ) (v : Fin n) (x : Fin n → Bool) :
    ElimFInv n (List.ofFn x) (List.ofFn (Function.update x v false)) (initFVar n v, []) := by
  refine ⟨by simp, by simp [initFVar], ?_⟩
  intro i
  by_cases hi : i < n
  · rw [initFVar, ofFn_getD_lt _ _ hi]
    by_cases heq : (⟨i, hi⟩ : Fin n) = v
    · simp only [heq, ↓reduceIte, optValid, optVal]
      rw [ofFn_getD_lt _ _ hi, heq, Function.update_self]
      exact ⟨trivial, rfl⟩
    · simp only [heq, ↓reduceIte, optValid, optVal, wiresFrom_nil]
      refine ⟨by omega, ?_⟩
      rw [ofFn_getD_lt _ _ hi, ofFn_getD_lt _ _ hi, Function.update_of_ne heq]
  · rw [List.getD_eq_default _ _ (by simp [initFVar]; omega),
        List.getD_eq_default _ _ (by simp; omega)]
    exact ⟨trivial, rfl⟩

/-- Count of OR gates dropped by `elimFPass` equals the number of input OR gates whose filtered inputs have length ≤ 1. -/
def isDroppedOr (n : ℕ) (gs : List Gate) (st0 : List (Option ℕ)) (j : ℕ) : Prop :=
  ∃ hj : j < gs.length, gs[j].op = GateOp.or ∧
    ((gs[j].inputs.map fun i => (elimFPass n (gs.take j) (st0, [])).1.getD i none).filterMap id).length ≤ 1

open Classical in
lemma elimFPass_orCount_add_dropped (n : ℕ) (gs : List Gate) (st0 : List (Option ℕ))
    (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ((elimFPass n gs (st0, [])).2.filter (fun g => isOrOp g.op)).length +
      ((Finset.range gs.length).filter (fun j =>
        let g := gs.getD j ⟨GateOp.and, []⟩
        g.op = GateOp.or ∧
        ((g.inputs.map fun i => (elimFPass n (gs.take j) (st0, [])).1.getD i none).filterMap id).length ≤ 1)).card =
      (gs.filter (fun g => isOrOp g.op)).length := by
  induction gs using List.reverseRecOn with
  | nil => simp [elimFPass]
  | append_singleton gs g ih =>
    have hgs' : ∀ g' ∈ gs, g'.op = GateOp.and ∨ g'.op = GateOp.or :=
      fun g' hg' => hgs g' (List.mem_append_left _ hg')
    have ih' := ih hgs'
    rw [elimFPass_append, elimFPass_cons, elimFPass_nil]
    rw [List.filter_append, List.length_append, List.length_append, List.length_singleton,
        Finset.range_add_one, Finset.filter_insert]
    have hprev : (Finset.range gs.length).filter (fun j =>
        let g' := (gs ++ [g]).getD j ⟨GateOp.and, []⟩
        g'.op = GateOp.or ∧
        ((g'.inputs.map fun i => (elimFPass n ((gs ++ [g]).take j) (st0, [])).1.getD i none).filterMap id).length ≤ 1) =
      (Finset.range gs.length).filter (fun j =>
        let g' := gs.getD j ⟨GateOp.and, []⟩
        g'.op = GateOp.or ∧
        ((g'.inputs.map fun i => (elimFPass n (gs.take j) (st0, [])).1.getD i none).filterMap id).length ≤ 1) := by
      apply Finset.filter_congr
      intro j hj
      rw [Finset.mem_range] at hj
      rw [getD_snoc_lt _ _ _ hj, List.take_append_of_le_length hj.le]
    have hlast_g : (gs ++ [g]).getD gs.length ⟨GateOp.and, []⟩ = g := getD_snoc_eq gs g _
    have hlast_take : (gs ++ [g]).take gs.length = gs := by
      rw [List.take_append_of_le_length le_rfl, List.take_length]
    rw [hprev, hlast_g, hlast_take]
    set acc := elimFPass n gs (st0, []) with hacc
    have hnotmem : gs.length ∉ (Finset.range gs.length).filter (fun j =>
        let g' := gs.getD j ⟨GateOp.and, []⟩
        g'.op = GateOp.or ∧
        ((g'.inputs.map fun i => (elimFPass n (gs.take j) (st0, [])).1.getD i none).filterMap id).length ≤ 1) := by
      simp
    rcases hgs g (by simp) with hop | hop
    · have hstep_or : ((elimFStep n acc g).2.filter (fun g' => isOrOp g'.op)).length =
          (acc.2.filter (fun g' => isOrOp g'.op)).length := by
        unfold elimFStep; rw [hop]; dsimp only
        split_ifs
        · rfl
        · simp [List.filter_append, isOrOp_and]
      rw [hstep_or]
      have hne_ao : ¬ (GateOp.and = GateOp.or) := fun h => by cases h
      simp only [hop, isOrOp_and, hne_ao, false_and, ↓reduceIte, List.filter_cons,
        Bool.false_eq_true, List.filter_nil, List.length_nil, Nat.add_zero]
      exact ih'
    · simp only [hop, true_and, List.filter_cons, isOrOp_or, ↓reduceIte, List.filter_nil, List.length_cons, List.length_nil, Nat.zero_add]
      set fm := (g.inputs.map fun i => acc.1.getD i none).filterMap id with hfm
      cases hfm_eq : fm with
      | nil =>
        have hstep_eq : (elimFStep n acc g).2 = acc.2 := by
          unfold elimFStep; rw [hop]; dsimp only; rw [← hfm, hfm_eq]
        rw [hstep_eq, if_pos (by simp), Finset.card_insert_of_notMem hnotmem]
        have := ih'; omega
      | cons w1 rest =>
        cases rest with
        | nil =>
          have hstep_eq : (elimFStep n acc g).2 = acc.2 := by
            unfold elimFStep; rw [hop]; dsimp only; rw [← hfm, hfm_eq]
          rw [hstep_eq, if_pos (by simp), Finset.card_insert_of_notMem hnotmem]
          have := ih'; omega
        | cons w2 rest2 =>
          have hstep_eq : (elimFStep n acc g).2 = acc.2 ++ [⟨GateOp.or, w1 :: w2 :: rest2⟩] := by
            unfold elimFStep; rw [hop]; dsimp only; rw [← hfm, hfm_eq]
          rw [hstep_eq, List.filter_append, List.length_append]
          have hf1 : ([Gate.mk GateOp.or (w1 :: w2 :: rest2)].filter (fun g : Gate => isOrOp g.op)).length = 1 := rfl
          rw [hf1, if_neg (by simp : ¬ (w1 :: w2 :: rest2).length ≤ 1)]
          dsimp only at ih' ⊢
          omega

/-! ### Deleting a single OR gate `j0` and replacing wire `n + j0` by wire `b < n + j0` -/

def rd (n j0 b u : ℕ) : ℕ :=
  if u < n + j0 then u else if u = n + j0 then b else u - 1

def rdelG (n j0 b : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (rd n j0 b)⟩

def rdelC (n j0 b : ℕ) (C : Circuit) : Circuit :=
  ⟨C.gates.take j0 ++ (C.gates.drop (j0 + 1)).map (rdelG n j0 b), rd n j0 b C.output⟩

lemma rdelC_mono2 (n j0 b : ℕ) (C : Circuit) (hmono : Monotone2 C) : Monotone2 (rdelC n j0 b C) := by
  intro g hg
  simp only [rdelC, List.mem_append, List.mem_map] at hg
  rcases hg with h | ⟨g', hg', rfl⟩
  · exact hmono g (List.mem_of_mem_take h)
  · obtain ⟨h1, h2⟩ := hmono g' (List.mem_of_mem_drop hg')
    exact ⟨h1, by simpa [rdelG] using h2⟩

lemma rdelC_orCount (n j0 b : ℕ) (C : Circuit) (hj0 : j0 < C.gates.length)
    (hor : (C.gates[j0]).op = GateOp.or) :
    orCount (rdelC n j0 b C) + 1 = orCount C := by
  unfold orCount rdelC
  have hsplit : C.gates = C.gates.take j0 ++ C.gates[j0] :: C.gates.drop (j0 + 1) := by simp
  conv_rhs => rw [hsplit]
  simp only [List.filter_append, List.length_append, List.filter_cons, hor, isOrOp_or, ↓reduceIte, List.length_cons]
  have hmap : ((C.gates.drop (j0 + 1)).map (rdelG n j0 b)).filter (fun g => isOrOp g.op) =
      ((C.gates.drop (j0 + 1)).filter (fun g => isOrOp g.op)).map (rdelG n j0 b) := by
    induction (C.gates.drop (j0 + 1)) with
    | nil => rfl
    | cons g gs ih =>
      simp only [List.map_cons, List.filter_cons, rdelG]
      cases h : isOrOp g.op <;> simp [h, ih, rdelG]
  rw [hmap, List.length_map]
  omega

lemma rdelC_eval_le_suffix (n j0 b : ℕ) (hb : b < n + j0) (gs : List Gate)
    (hmono : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ (W W' : List Bool), W.length = W'.length + 1 → n + j0 ≤ W'.length →
      (∀ u : ℕ, W'.getD (rd n j0 b u) false = true → W.getD u false = true) →
      ∀ u : ℕ, (wiresFrom (gs.map (rdelG n j0 b)) W').getD (rd n j0 b u) false = true →
        (wiresFrom gs W).getD u false = true := by
  induction gs with
  | nil => intro W W' _ _ h u; exact h u
  | cons g gs ih =>
    intro W W' hlen hge h u
    rw [List.map_cons, wiresFrom_cons, wiresFrom_cons]
    have hstep : (rdelG n j0 b g).op.eval ((rdelG n j0 b g).inputs.map fun i => W'.getD i false) = true →
        g.op.eval (g.inputs.map fun i => W.getD i false) = true := by
      simp only [rdelG, List.map_map]
      apply eval_mono_op g.op (hmono g List.mem_cons_self) _ _ (by simp)
      intro k hk h1
      simp only [List.getElem_map, Function.comp_apply] at h1 ⊢
      exact h _ h1
    apply ih (fun g' hg' => hmono g' (List.mem_cons_of_mem _ hg')) _ _ (by simp; omega) (by simp; omega)
    intro v hv
    rcases Nat.lt_trichotomy v W.length with hlt | heq | hgt
    · have hv' : rd n j0 b v < W'.length := by unfold rd; split_ifs <;> omega
      rw [getD_snoc_lt _ _ _ hv'] at hv
      rw [getD_snoc_lt _ _ _ hlt]
      exact h v hv
    · have hv' : rd n j0 b v = W'.length := by unfold rd; split_ifs <;> omega
      rw [hv', getD_snoc_eq] at hv
      rw [heq, getD_snoc_eq]
      exact hstep hv
    · have hv' : W'.length + 1 ≤ rd n j0 b v := by unfold rd; split_ifs <;> omega
      rw [List.getD_eq_default _ _ (by simp; omega)] at hv
      cases hv

lemma rdelC_eval_eq_suffix (n j0 b : ℕ) (hb : b < n + j0) (gs : List Gate) :
    ∀ (W W' : List Bool), W.length = W'.length + 1 → n + j0 ≤ W'.length →
      (∀ u : ℕ, W'.getD (rd n j0 b u) false = W.getD u false) →
      ∀ u : ℕ, (wiresFrom (gs.map (rdelG n j0 b)) W').getD (rd n j0 b u) false =
        (wiresFrom gs W).getD u false := by
  induction gs with
  | nil => intro W W' _ _ h u; exact h u
  | cons g gs ih =>
    intro W W' hlen hge h u
    rw [List.map_cons, wiresFrom_cons, wiresFrom_cons]
    have hstep : (rdelG n j0 b g).op.eval ((rdelG n j0 b g).inputs.map fun i => W'.getD i false) =
        g.op.eval (g.inputs.map fun i => W.getD i false) := by
      simp only [rdelG, List.map_map]
      congr 1; apply List.map_congr_left; intro i _; exact h i
    rw [hstep]
    apply ih _ _ (by simp; omega) (by simp; omega)
    intro v
    rcases Nat.lt_trichotomy v W.length with hlt | heq | hgt
    · have hv' : rd n j0 b v < W'.length := by unfold rd; split_ifs <;> omega
      rw [getD_snoc_lt _ _ _ hv', getD_snoc_lt _ _ _ hlt]
      exact h v
    · have hv' : rd n j0 b v = W'.length := by unfold rd; split_ifs <;> omega
      rw [hv', heq, getD_snoc_eq, getD_snoc_eq]
    · have hv' : W'.length + 1 ≤ rd n j0 b v := by unfold rd; split_ifs <;> omega
      rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

lemma rdelC_eval_le {n j0 b : ℕ} {C : Circuit} (hmono : Monotone2 C) (hj0 : j0 < C.gates.length)
    (hb : b < n + j0) (x : Fin n → Bool)
    (hle : (wiresFrom C.gates (List.ofFn x)).getD b false = true →
      (wiresFrom C.gates (List.ofFn x)).getD (n + j0) false = true) :
    (rdelC n j0 b C).eval (List.ofFn x) = true → C.eval (List.ofFn x) = true := by
  have hsplit : C.gates = C.gates.take j0 ++ C.gates[j0] :: C.gates.drop (j0 + 1) := by simp
  set W0 := wiresFrom (C.gates.take j0) (List.ofFn x)
  have hW0len : W0.length = n + j0 := by
    rw [wiresFrom_length, List.length_ofFn, List.length_take, Nat.min_eq_left hj0.le]
  set v0 := (C.gates[j0]).op.eval ((C.gates[j0]).inputs.map fun i => W0.getD i false)
  have hCsplit : wiresFrom C.gates (List.ofFn x) = wiresFrom (C.gates.drop (j0 + 1)) (W0 ++ [v0]) := by
    conv_lhs => rw [hsplit, wiresFrom_append, wiresFrom_cons]
  have hC'split : wiresFrom (rdelC n j0 b C).gates (List.ofFn x) =
      wiresFrom ((C.gates.drop (j0 + 1)).map (rdelG n j0 b)) W0 := by
    simp only [rdelC, wiresFrom_append, W0]
  change (wiresFrom (rdelC n j0 b C).gates (List.ofFn x)).getD (rd n j0 b C.output) false = true →
    (wiresFrom C.gates (List.ofFn x)).getD C.output false = true
  rw [hCsplit, hC'split]
  apply rdelC_eval_le_suffix n j0 b hb (C.gates.drop (j0 + 1))
    (fun g hg => (hmono g (List.mem_of_mem_drop hg)).1) (W0 ++ [v0]) W0 (by simp) (by omega)
  intro u hu
  rcases Nat.lt_trichotomy u (n + j0) with hlt | heq | hgt
  · have hru : rd n j0 b u = u := by unfold rd; simp [hlt]
    rw [hru] at hu
    rw [getD_snoc_lt _ _ _ (by omega)]
    exact hu
  · subst heq
    have hru : rd n j0 b (n + j0) = b := by unfold rd; simp
    rw [hru] at hu
    rw [← hW0len, getD_snoc_eq]
    have hb_eq : (wiresFrom C.gates (List.ofFn x)).getD b false = W0.getD b false := by
      rw [hCsplit, wiresFrom_getD_lt _ _ (by simp [hW0len]; omega), getD_snoc_lt _ _ _ (by omega)]
    have hj_eq : (wiresFrom C.gates (List.ofFn x)).getD (n + j0) false = v0 := by
      rw [hCsplit, wiresFrom_getD_lt _ _ (by simp [hW0len]), ← hW0len, getD_snoc_eq]
    rw [← hj_eq]
    exact hle (hb_eq.symm ▸ hu)
  · have hru : rd n j0 b u = u - 1 := by unfold rd; rw [if_neg (by omega), if_neg (by omega)]
    rw [hru, List.getD_eq_default _ _ (by omega)] at hu
    cases hu

lemma rdelC_eval_eq {n j0 b : ℕ} {C : Circuit} (hj0 : j0 < C.gates.length)
    (hb : b < n + j0) (x : Fin n → Bool)
    (heq_val : (wiresFrom C.gates (List.ofFn x)).getD b false =
      (wiresFrom C.gates (List.ofFn x)).getD (n + j0) false) :
    (rdelC n j0 b C).eval (List.ofFn x) = C.eval (List.ofFn x) := by
  have hsplit : C.gates = C.gates.take j0 ++ C.gates[j0] :: C.gates.drop (j0 + 1) := by simp
  set W0 := wiresFrom (C.gates.take j0) (List.ofFn x)
  have hW0len : W0.length = n + j0 := by
    rw [wiresFrom_length, List.length_ofFn, List.length_take, Nat.min_eq_left hj0.le]
  set v0 := (C.gates[j0]).op.eval ((C.gates[j0]).inputs.map fun i => W0.getD i false)
  have hCsplit : wiresFrom C.gates (List.ofFn x) = wiresFrom (C.gates.drop (j0 + 1)) (W0 ++ [v0]) := by
    conv_lhs => rw [hsplit, wiresFrom_append, wiresFrom_cons]
  have hC'split : wiresFrom (rdelC n j0 b C).gates (List.ofFn x) =
      wiresFrom ((C.gates.drop (j0 + 1)).map (rdelG n j0 b)) W0 := by
    simp only [rdelC, wiresFrom_append, W0]
  change (wiresFrom (rdelC n j0 b C).gates (List.ofFn x)).getD (rd n j0 b C.output) false =
    (wiresFrom C.gates (List.ofFn x)).getD C.output false
  rw [hCsplit, hC'split]
  apply rdelC_eval_eq_suffix n j0 b hb (C.gates.drop (j0 + 1)) (W0 ++ [v0]) W0 (by simp) (by omega)
  intro u
  rcases Nat.lt_trichotomy u (n + j0) with hlt | heq | hgt
  · have hru : rd n j0 b u = u := by unfold rd; simp [hlt]
    rw [hru, getD_snoc_lt _ _ _ (by omega)]
  · subst heq
    have hru : rd n j0 b (n + j0) = b := by unfold rd; simp
    rw [hru, ← hW0len, getD_snoc_eq]
    have hb_eq : (wiresFrom C.gates (List.ofFn x)).getD b false = W0.getD b false := by
      rw [hCsplit, wiresFrom_getD_lt _ _ (by simp [hW0len]; omega), getD_snoc_lt _ _ _ (by omega)]
    have hj_eq : (wiresFrom C.gates (List.ofFn x)).getD (n + j0) false = v0 := by
      rw [hCsplit, wiresFrom_getD_lt _ _ (by simp [hW0len]), ← hW0len, getD_snoc_eq]
    rw [← hb_eq, ← hj_eq]; exact heq_val
  · have hru : rd n j0 b u = u - 1 := by unfold rd; rw [if_neg (by omega), if_neg (by omega)]
    rw [hru, List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by simp; omega)]

/-! ### AND-only initSeg characterization -/

lemma and_initSeg_char {n : ℕ} {gs : List Gate} {j0 : ℕ} (hj0 : j0 ≤ gs.length)
    (hand : ∀ j < j0, (gs.getD j ⟨GateOp.and, []⟩).op = GateOp.and) :
    ∀ w < n + j0,
      (∀ x : Fin n → Bool, (wiresFrom gs (List.ofFn x)).getD w false = false) ∨
      ∃ S : Finset (Fin n), ∀ x : Fin n → Bool,
        (wiresFrom gs (List.ofFn x)).getD w false = true ↔ ∀ i ∈ S, x i = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    by_cases hlt : w < n
    · right
      refine ⟨{⟨w, hlt⟩}, fun x => ?_⟩
      rw [wiresFrom_getD_lt _ _ (by simp; exact hlt), ofFn_getD_lt _ _ hlt]
      simp
    · have hj : w - n < j0 := by omega
      have hjlen : w - n < gs.length := by omega
      have hweq : n + (w - n) = w := by omega
      have hop : (gs[w - n]).op = GateOp.and := by
        have := hand (w - n) hj; rwa [List.getD_eq_getElem _ _ hjlen] at this
      by_cases hoob : ∃ i ∈ (gs[w - n]).inputs, n + (w - n) ≤ i
      · left
        obtain ⟨i, hi, hige⟩ := hoob
        intro x
        have hgd := wiresFrom_gate_getD gs (List.ofFn x) hjlen
        simp only [List.length_ofFn, hweq, hop] at hgd
        rw [hgd]
        simp only [GateOp.eval]
        apply Bool.eq_false_iff.2; intro hall
        rw [List.all_eq_true] at hall
        have hlen : (wiresFrom (gs.take (w - n)) (List.ofFn x)).length = n + (w - n) := by
          rw [wiresFrom_length, List.length_ofFn, List.length_take, Nat.min_eq_left hjlen.le]
        have hf : (wiresFrom (gs.take (w - n)) (List.ofFn x)).getD i false = false :=
          List.getD_eq_default _ _ (by omega)
        have h1 := hall false (List.mem_map.2 ⟨i, hi, hf⟩)
        cases h1
      · push_neg at hoob
        have hrec : ∀ i ∈ (gs[w - n]).inputs,
            (∀ x, (wiresFrom gs (List.ofFn x)).getD i false = false) ∨
            ∃ S : Finset (Fin n), ∀ x, (wiresFrom gs (List.ofFn x)).getD i false = true ↔ ∀ k ∈ S, x k = true :=
          fun i hi => ih i (by have := hoob i hi; omega) (by have := hoob i hi; omega)
        by_cases hzero : ∃ i ∈ (gs[w - n]).inputs, ∀ x : Fin n → Bool, (wiresFrom gs (List.ofFn x)).getD i false = false
        · left
          obtain ⟨i, hi, hif⟩ := hzero
          intro x
          have hgd := wiresFrom_gate_getD gs (List.ofFn x) hjlen
          simp only [List.length_ofFn, hweq, hop] at hgd
          rw [hgd]
          simp only [GateOp.eval]
          apply Bool.eq_false_iff.2; intro hall
          rw [List.all_eq_true] at hall
          have hti : (wiresFrom (gs.take (w - n)) (List.ofFn x)).getD i false = false := by
            rw [wiresFrom_take_getD _ _ hjlen (by simp; exact hoob i hi)]; exact hif x
          have h1 := hall false (List.mem_map.2 ⟨i, hi, hti⟩)
          cases h1
        · push_neg at hzero
          classical
          have hex : ∀ i ∈ (gs[w - n]).inputs,
              ∃ S : Finset (Fin n), ∀ x, (wiresFrom gs (List.ofFn x)).getD i false = true ↔ ∀ k ∈ S, x k = true := by
            intro i hi
            rcases hrec i hi with hf | ⟨S, hS⟩
            · obtain ⟨x, hx⟩ := hzero i hi; exact absurd (hf x) hx
            · exact ⟨S, hS⟩
          right
          let S : Finset (Fin n) := (gs[w - n]).inputs.toFinset.biUnion fun i =>
            if h : i ∈ (gs[w - n]).inputs then Classical.choose (hex i h) else ∅
          refine ⟨S, fun x => ?_⟩
          have hgd := wiresFrom_gate_getD gs (List.ofFn x) hjlen
          simp only [List.length_ofFn, hweq, hop] at hgd
          rw [hgd]
          simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq, forall_exists_index, and_imp,
            forall_apply_eq_imp_iff₂]
          constructor
          · intro hall k hk
            simp only [S, Finset.mem_biUnion, List.mem_toFinset] at hk
            obtain ⟨i, hi, hki⟩ := hk
            rw [dif_pos hi] at hki
            have h1 := hall i hi
            rw [wiresFrom_take_getD _ _ hjlen (by simp; exact hoob i hi)] at h1
            exact (Classical.choose_spec (hex i hi) x).1 h1 k hki
          · intro hall i hi
            rw [wiresFrom_take_getD _ _ hjlen (by simp; exact hoob i hi)]
            apply (Classical.choose_spec (hex i hi) x).2
            intro k hk
            apply hall k
            simp only [S, Finset.mem_biUnion, List.mem_toFinset]
            exact ⟨i, hi, by rw [dif_pos hi]; exact hk⟩

/-! ### Replace a single gate `j0` with constant `true` (`⟨GateOp.and, []⟩`) -/

def setTrueC (j0 : ℕ) (C : Circuit) : Circuit :=
  ⟨C.gates.set j0 ⟨GateOp.and, []⟩, C.output⟩

lemma setTrueC_mono2 (j0 : ℕ) (C : Circuit) (hmono : Monotone2 C) : Monotone2 (setTrueC j0 C) := by
  intro g hg
  by_cases hj0 : j0 < C.gates.length
  · simp only [setTrueC, List.set_eq_take_cons_drop ⟨GateOp.and, []⟩ hj0, List.mem_append, List.mem_cons] at hg
    rcases hg with h | rfl | h
    · exact hmono g (List.mem_of_mem_take h)
    · exact ⟨by simp, by simp⟩
    · exact hmono g (List.mem_of_mem_drop h)
  · simp only [setTrueC, List.set_eq_of_length_le (Nat.le_of_not_lt hj0)] at hg
    exact hmono g hg

lemma setTrueC_orCount (j0 : ℕ) (C : Circuit) (hj0 : j0 < C.gates.length)
    (hor : (C.gates[j0]).op = GateOp.or) :
    orCount (setTrueC j0 C) + 1 = orCount C := by
  unfold orCount setTrueC
  have h1 : C.gates = C.gates.take j0 ++ C.gates[j0] :: C.gates.drop (j0 + 1) := by simp
  have h2 : C.gates.set j0 ⟨GateOp.and, []⟩ = C.gates.take j0 ++ ⟨GateOp.and, []⟩ :: C.gates.drop (j0 + 1) := by
    rw [List.set_eq_take_cons_drop ⟨GateOp.and, []⟩ hj0]
  conv_rhs => rw [h1]
  rw [h2]
  simp only [List.filter_append, List.length_append, List.filter_cons, hor, isOrOp_or, isOrOp_and, ↓reduceIte, Bool.false_eq_true, List.length_cons]
  omega

lemma setTrueC_eval (j0 : ℕ) (C : Circuit) (hj0 : j0 < C.gates.length) (x : Fin n → Bool)
    (ht : (wiresFrom C.gates (List.ofFn x)).getD (n + j0) false = true) :
    (setTrueC j0 C).eval (List.ofFn x) = C.eval (List.ofFn x) := by
  have h1 : C.gates = C.gates.take j0 ++ C.gates[j0] :: C.gates.drop (j0 + 1) := by simp
  have h2 : (setTrueC j0 C).gates = C.gates.take j0 ++ ⟨GateOp.and, []⟩ :: C.gates.drop (j0 + 1) := by
    simp only [setTrueC]; rw [List.set_eq_take_cons_drop ⟨GateOp.and, []⟩ hj0]
  set W0 := wiresFrom (C.gates.take j0) (List.ofFn x)
  have hW0len : W0.length = n + j0 := by
    rw [wiresFrom_length, List.length_ofFn, List.length_take, Nat.min_eq_left hj0.le]
  have hv : (C.gates[j0]).op.eval ((C.gates[j0]).inputs.map fun i => W0.getD i false) = true := by
    have := wiresFrom_gate_getD C.gates (List.ofFn x) hj0
    simp only [List.length_ofFn] at this
    rw [← this]; exact ht
  change (wiresFrom (setTrueC j0 C).gates (List.ofFn x)).getD C.output false =
    (wiresFrom C.gates (List.ofFn x)).getD C.output false
  conv_rhs => rw [h1, wiresFrom_append, wiresFrom_cons]
  rw [h2, wiresFrom_append, wiresFrom_cons, hv]
  rfl

/-! ### Replace a single gate `j0` with constant `false` (`⟨GateOp.or, []⟩`) is NOT reducing OR count;
    instead use `elimFPass` with `initFGate` when we want to set a single gate `j0` to `false`! -/

def elimFGateC (n j0 : ℕ) (C : Circuit) : Circuit :=
  let pre := C.gates.take j0
  let post := C.gates.drop (j0 + 1)
  let acc0 : List (Option ℕ) × List Gate := (List.ofFn (fun i : Fin (n + j0) => some i.val) ++ [none], pre)
  let acc := elimFPass n post acc0
  ⟨acc.2, (acc.1.getD C.output none).getD (n + acc.2.length)⟩

lemma elimFGateC_spec (n j0 : ℕ) (C : Circuit) (hmono : Monotone2 C) (hj0 : j0 < C.gates.length)
    (hf : ∀ x : Fin n → Bool, (wiresFrom C.gates (List.ofFn x)).getD (n + j0) false = false) :
    Monotone2 (elimFGateC n j0 C) ∧
    (C.gates[j0].op = GateOp.or → orCount (elimFGateC n j0 C) + 1 ≤ orCount C) ∧
    ∀ x : Fin n → Bool, (elimFGateC n j0 C).eval (List.ofFn x) = C.eval (List.ofFn x) := by
  let pre := C.gates.take j0
  let post := C.gates.drop (j0 + 1)
  let acc0 : List (Option ℕ) × List Gate := (List.ofFn (fun i : Fin (n + j0) => some i.val) ++ [none], pre)
  let acc := elimFPass n post acc0
  have hpre_ok : ∀ g ∈ pre, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 :=
    fun g hg => hmono g (List.mem_of_mem_take hg)
  have hpost_ok : ∀ g ∈ post, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 :=
    fun g hg => hmono g (List.mem_of_mem_drop hg)
  have hmono' : Monotone2 (elimFGateC n j0 C) := elimFPass_mono2 n post acc0 hpre_ok hpost_ok
  have hor_le : ∀ (gs : List Gate) (a : List (Option ℕ) × List Gate),
      (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) →
      ((elimFPass n gs a).2.filter (fun g => isOrOp g.op)).length ≤
        (a.2.filter (fun g => isOrOp g.op)).length +
        (gs.filter (fun g => isOrOp g.op)).length := by
    intro gs
    induction gs with
    | nil => intro a _; simp [elimFPass]
    | cons g gs ih =>
      intro a hgs
      rw [elimFPass_cons]
      have h1 := ih (elimFStep n a g) (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg'))
      have hstep : ((elimFStep n a g).2.filter (fun g' => isOrOp g'.op)).length ≤
          (a.2.filter (fun g' => isOrOp g'.op)).length +
          if isOrOp g.op = true then 1 else 0 := by
        unfold elimFStep
        rcases hgs g List.mem_cons_self with hop | hop
        · rw [hop]; dsimp only
          by_cases hany : (g.inputs.map fun i => a.1.getD i none).any Option.isNone = true
          · rw [if_pos hany]; simp [isOrOp_and]
          · rw [if_neg hany]; simp [List.filter_append, List.filter_cons, isOrOp_and]
        · rw [hop]; dsimp only
          split
          · simp [isOrOp_or]
          · simp [isOrOp_or]
          · simp only [List.filter_append, List.length_append, List.filter_cons, List.filter_nil,
              isOrOp_or, ↓reduceIte, List.length_cons, List.length_nil]
            omega
      simp only [List.filter_cons]
      cases hg : isOrOp g.op <;> simp [hg] at hstep ⊢ <;> omega
  refine ⟨hmono', ?_, ?_⟩
  · intro hor
    have h1 := hor_le post acc0 (fun g hg => (hpost_ok g hg).1)
    have hsplit : C.gates = pre ++ C.gates[j0] :: post := by simp [pre, post]
    change (acc.2.filter (fun g => isOrOp g.op)).length + 1 ≤
      (C.gates.filter (fun g => isOrOp g.op)).length
    conv_rhs => rw [hsplit]
    simp only [List.filter_append, List.length_append, List.filter_cons, hor, isOrOp_or, ↓reduceIte, List.length_cons]
    dsimp only [acc0] at h1
    change (acc.2.filter (fun g => isOrOp g.op)).length ≤ (pre.filter (fun g => isOrOp g.op)).length + (post.filter (fun g => isOrOp g.op)).length at h1
    omega
  · intro x
    have hinv0 : ElimFInv n (List.ofFn x) (wiresFrom (pre ++ [C.gates[j0]]) (List.ofFn x)) acc0 := by
      set W0 := wiresFrom pre (List.ofFn x)
      have hW0 : W0.length = n + j0 := by
        rw [wiresFrom_length, List.length_ofFn, List.length_take, Nat.min_eq_left hj0.le]
      have hv0 : (C.gates[j0]).op.eval ((C.gates[j0]).inputs.map fun i => W0.getD i false) = false := by
        have := wiresFrom_gate_getD C.gates (List.ofFn x) hj0
        simp only [List.length_ofFn] at this
        rw [← this]; exact hf x
      have hW1 : wiresFrom (pre ++ [C.gates[j0]]) (List.ofFn x) = W0 ++ [false] := by
        rw [wiresFrom_append, wiresFrom_cons, wiresFrom_nil, hv0]
      rw [hW1]
      refine ⟨by simp, by simp [acc0, hW0], ?_⟩
      intro i
      by_cases hlt : i < n + j0
      · have hst : acc0.1.getD i none = some i := by
          simp only [acc0]
          rw [getD_snoc_lt _ _ _ (by simp; exact hlt), ofFn_getD_lt (fun k : Fin (n + j0) => some k.val) none hlt]
        rw [hst, getD_snoc_lt _ _ _ (by omega)]
        simp only [optValid, optVal, acc0, pre, List.length_take, Nat.min_eq_left hj0.le]
        exact ⟨hlt, rfl⟩
      · by_cases heq : i = n + j0
        · subst heq
          have hst : acc0.1.getD (n + j0) none = none := by
            simp only [acc0]
            have h := getD_snoc_eq (List.ofFn fun i : Fin (n + j0) => some i.val) none none
            simpa using h
          rw [hst, ← hW0, getD_snoc_eq]
          exact ⟨trivial, rfl⟩
        · rw [List.getD_eq_default _ _ (by simp [acc0]; omega),
              List.getD_eq_default _ _ (by simp [hW0]; omega)]
          exact ⟨trivial, rfl⟩
    have hinv := elimFInv_pass n (List.ofFn x) post _ acc0 (fun g hg => (hpost_ok g hg).1) hinv0
    have hsplit : C.gates = (pre ++ [C.gates[j0]]) ++ post := by simp [pre, post]
    have hCE : wiresFrom post (wiresFrom (pre ++ [C.gates[j0]]) (List.ofFn x)) =
        wiresFrom C.gates (List.ofFn x) := by
      conv_rhs => rw [hsplit, wiresFrom_append]
    rw [hCE] at hinv
    have hval := (hinv.2.2 C.output).2
    change (wiresFrom acc.2 (List.ofFn x)).getD ((acc.1.getD C.output none).getD (n + acc.2.length)) false =
      (wiresFrom C.gates (List.ofFn x)).getD C.output false
    cases hst : acc.1.getD C.output none with
    | none =>
      rw [hst] at hval
      simp only [Option.getD_none]
      rw [List.getD_eq_default _ _ (by rw [wiresFrom_length, List.length_ofFn])]
      exact hval
    | some k =>
      rw [hst] at hval
      simpa [optVal] using hval

/-! ### Main induction theorem on `G.edgeSet.ncard` -/

theorem main_599 : ∀ (m n : ℕ) (G : SimpleGraph (Fin n)) (C : Circuit),
    G.edgeSet.ncard = m →
    (∀ S : Finset (Fin n), {e : Sym2 (Fin n) | e ∈ G.edgeSet ∧ ∀ v ∈ e, v ∈ S}.ncard ≤ S.card) →
    (∀ (v : Fin n) (c : G.Walk v v), c.IsCycle → c.length ≠ 4) →
    Monotone2 C →
    ComputesEdges G C →
    G.edgeSet.ncard ≤ orCount C + 1 := by
  intro m
  induction m using Nat.strong_induction_on with
  | ind m ih =>
    intro n G C hm hsparse hnoC4 hmono hcomp
    classical
    by_cases hm1 : m ≤ 1
    · omega
    -- Replace C with a Monotone2 circuit satisfying ComputesEdges G with MINIMUM orCount!
    have hex_min : ∃ k : ℕ, ∃ D : Circuit, Monotone2 D ∧ ComputesEdges G D ∧ orCount D = k :=
      ⟨orCount C, C, hmono, hcomp, rfl⟩
    let k0 := Nat.find hex_min
    have hk0_le : k0 ≤ orCount C := Nat.find_min' hex_min ⟨C, hmono, hcomp, rfl⟩
    obtain ⟨D, hDmono, hDcomp, hDor⟩ := Nat.find_spec hex_min
    have hDmin : ∀ D' : Circuit, Monotone2 D' → ComputesEdges G D' → orCount D ≤ orCount D' := by
      intro D' h1 h2; rw [hDor]; exact Nat.find_min' hex_min ⟨D', h1, h2, rfl⟩
    suffices hgoal : G.edgeSet.ncard ≤ orCount D + 1 by omega
    -- Helper: removing one vertex v from G preserves hsparse, hnoC4, and yields ComputesEdges on elimFPass
    have hdel_vertex : ∀ (v : Fin n),
        let G' : SimpleGraph (Fin n) := SimpleGraph.fromRel (fun a b => G.Adj a b ∧ a ≠ v ∧ b ≠ v)
        (∀ a b, G'.Adj a b ↔ G.Adj a b ∧ a ≠ v ∧ b ≠ v) ∧
        (∀ S : Finset (Fin n), {e : Sym2 (Fin n) | e ∈ G'.edgeSet ∧ ∀ u ∈ e, u ∈ S}.ncard ≤ S.card) ∧
        (∀ (w : Fin n) (c : G'.Walk w w), c.IsCycle → c.length ≠ 4) := by
      intro v
      let G' : SimpleGraph (Fin n) := SimpleGraph.fromRel (fun a b => G.Adj a b ∧ a ≠ v ∧ b ≠ v)
      have hG'adj : ∀ a b, G'.Adj a b ↔ G.Adj a b ∧ a ≠ v ∧ b ≠ v := by
        intro a b
        simp only [G', SimpleGraph.fromRel_adj]
        constructor
        · rintro ⟨_, (⟨h, ha, hb⟩ | ⟨h, hb, ha⟩)⟩
          · exact ⟨h, ha, hb⟩
          · exact ⟨h.symm, ha, hb⟩
        · rintro ⟨h, ha, hb⟩
          exact ⟨fun e => G.irrefl (e ▸ h), Or.inl ⟨h, ha, hb⟩⟩
      refine ⟨hG'adj, ?_, ?_⟩
      · intro S
        have hsub : {e : Sym2 (Fin n) | e ∈ G'.edgeSet ∧ ∀ u ∈ e, u ∈ S} ⊆
            {e : Sym2 (Fin n) | e ∈ G.edgeSet ∧ ∀ u ∈ e, u ∈ S} := by
          intro e ⟨he, hS⟩
          refine ⟨?_, hS⟩
          induction e using Sym2.ind with
          | _ a b => exact ((hG'adj a b).1 he).1
        exact (Set.ncard_le_ncard hsub (Set.toFinite _)).trans (hsparse S)
      · intro w c hc
        have hhom : G' ≤ G := fun a b hab => ((hG'adj a b).1 hab).1
        have hc' := hc.map (f := SimpleGraph.Hom.ofLE hhom) Function.injective_id
        have hlen := SimpleGraph.Walk.length_map (SimpleGraph.Hom.ofLE hhom) c
        rw [← hlen]
        exact hnoC4 w _ hc'
    -- Helper: elimFPass at x_v = false gives a valid circuit for G - v
    have helim_v : ∀ (v : Fin n),
        let acc := elimFPass n D.gates (initFVar n v, [])
        ∀ (out : ℕ), acc.1.getD D.output none = some out →
        let D' : Circuit := ⟨acc.2, out⟩
        let G' : SimpleGraph (Fin n) := SimpleGraph.fromRel (fun a b => G.Adj a b ∧ a ≠ v ∧ b ≠ v)
        Monotone2 D' ∧ ComputesEdges G' D' := by
      intro v acc out hout D' G'
      have hG'adj := (hdel_vertex v).1
      have hD'mono : Monotone2 D' := elimFPass_mono2 n D.gates (initFVar n v, []) (by simp) hDmono
      have hD'eval : ∀ x : Fin n → Bool, D'.eval (List.ofFn x) = D.eval (List.ofFn (Function.update x v false)) := by
        intro x
        have hinv := elimFInv_pass n (List.ofFn x) D.gates _ (initFVar n v, [])
          (fun g hg => (hDmono g hg).1) (elimFInv_initFVar n v x)
        have hval := (hinv.2.2 D.output).2
        rw [hout] at hval
        exact hval
      refine ⟨hD'mono, ?_, ?_, ?_⟩
      · intro a b hab
        have ⟨habG, hav, hbv⟩ := (hG'adj a b).1 hab
        rw [hD'eval]
        have hupd : Function.update (pairVec a b) v false = pairVec a b := by
          funext i
          by_cases hiv : i = v
          · subst hiv; simp [pairVec, hav.symm, hbv.symm]
          · rw [Function.update_of_ne hiv]
        rw [hupd]; exact hDcomp.1 a b habG
      · intro w
        rw [hD'eval]
        apply Bool.eq_false_iff.2; intro ht
        have h1 : D.eval (List.ofFn (unitVec w)) = true :=
          circuit_mono hDmono (fun i hi => by
            by_cases hiv : i = v
            · subst hiv; simp at hi
            · rwa [Function.update_of_ne hiv] at hi) ht
        rw [hDcomp.2.1 w] at h1; cases h1
      · intro a b hnot
        rw [hD'eval]
        apply Bool.eq_false_iff.2; intro ht
        by_cases hav : a = v
        · subst hav
          have h1 : D.eval (List.ofFn (unitVec b)) = true :=
            circuit_mono hDmono (fun i hi => by
              by_cases hiv : i = a
              · subst hiv; simp at hi
              · rw [Function.update_of_ne hiv] at hi
                simp only [pairVec, decide_eq_true_eq] at hi
                rcases hi with rfl | rfl
                · exact absurd rfl hiv
                · simp [unitVec]) ht
          rw [hDcomp.2.1 b] at h1; cases h1
        · by_cases hbv : b = v
          · subst hbv
            have h1 : D.eval (List.ofFn (unitVec a)) = true :=
              circuit_mono hDmono (fun i hi => by
                by_cases hiv : i = b
                · subst hiv; simp at hi
                · rw [Function.update_of_ne hiv] at hi
                  simp only [pairVec, decide_eq_true_eq] at hi
                  rcases hi with rfl | rfl
                  · simp [unitVec]
                  · exact absurd rfl hiv) ht
            rw [hDcomp.2.1 a] at h1; cases h1
          · have hnotG : ¬ G.Adj a b := fun h => hnot ((hG'adj a b).2 ⟨h, hav, hbv⟩)
            have h1 : D.eval (List.ofFn (pairVec a b)) = true :=
              circuit_mono hDmono (fun i hi => by
                by_cases hiv : i = v
                · subst hiv; simp at hi
                · rwa [Function.update_of_ne hiv] at hi) ht
            rw [hDcomp.2.2 a b hnotG] at h1; cases h1
    -- Case split: does G have a degree-1 vertex?
    by_cases hleaf : ∃ v : Fin n, G.degree v = 1
    · -- CASE 1: G has a leaf v!
      obtain ⟨v, hdegv⟩ := hleaf
      have hnv : (G.neighborFinset v).card = 1 := by simpa [SimpleGraph.card_neighborFinset_eq_degree] using hdegv
      obtain ⟨u, hu_mem⟩ := Finset.card_eq_one.1 hnv
      have huv : G.Adj v u := by
        have : u ∈ G.neighborFinset v := by rw [hu_mem]; simp
        exact (SimpleGraph.mem_neighborFinset G v u).1 this
      have hv_uniq : ∀ w, G.Adj v w → w = u := by
        intro w hvw
        have : w ∈ G.neighborFinset v := (SimpleGraph.mem_neighborFinset G v w).2 hvw
        rw [hu_mem, Finset.mem_singleton] at this; exact this
      let G' : SimpleGraph (Fin n) := SimpleGraph.fromRel (fun a b => G.Adj a b ∧ a ≠ v ∧ b ≠ v)
      have ⟨hG'adj, hG'sparse, hG'noC4⟩ := hdel_vertex v
      have hE' : G'.edgeSet = G.edgeSet \ {s(v, u)} := by
        ext e
        induction e using Sym2.ind with
        | _ a b =>
          rw [Set.mem_diff, Set.mem_singleton_iff, SimpleGraph.mem_edgeSet, SimpleGraph.mem_edgeSet, hG'adj]
          constructor
          · rintro ⟨hab, hav, hbv⟩
            refine ⟨hab, fun he => ?_⟩
            rcases Sym2.eq_iff.1 he with ⟨rfl, _⟩ | ⟨_, rfl⟩
            · exact hav rfl
            · exact hbv rfl
          · rintro ⟨hab, hne⟩
            refine ⟨hab, ?_, ?_⟩
            · intro rfl; exact hne (by rw [hv_uniq b hab])
            · intro rfl; exact hne (by rw [hv_uniq a hab.symm, Sym2.eq_swap])
      have hcard_G' : G'.edgeSet.ncard + 1 = G.edgeSet.ncard := by
        rw [hE', Set.ncard_diff_singleton_of_mem ((SimpleGraph.mem_edgeSet G).2 huv)]
        omega
      have hG'_nonempty : ∃ a b : Fin n, G'.Adj a b := by
        have hpos : 0 < G'.edgeSet.ncard := by omega
        obtain ⟨e, he⟩ := Set.nonempty_of_ncard_ne_zero (by omega : G'.edgeSet.ncard ≠ 0)
        induction e using Sym2.ind with
        | _ a b => exact ⟨a, b, he⟩
      set acc := elimFPass n D.gates (initFVar n v, []) with hacc
      -- Output cannot be none because G' has an edge
      have hout_some : ∃ out, acc.1.getD D.output none = some out := by
        cases hst : acc.1.getD D.output none with
        | some out => exact ⟨out, rfl⟩
        | none =>
          exfalso
          obtain ⟨a, b, hab⟩ := hG'_nonempty
          have ⟨habG, hav, hbv⟩ := (hG'adj a b).1 hab
          have hinv := elimFInv_pass n (List.ofFn (pairVec a b)) D.gates _ (initFVar n v, [])
            (fun g hg => (hDmono g hg).1) (elimFInv_initFVar n v (pairVec a b))
          have hval := (hinv.2.2 D.output).2
          rw [← hacc, hst] at hval
          have hupd : Function.update (pairVec a b) v false = pairVec a b := by
            funext i; by_cases hiv : i = v
            · subst hiv; simp [pairVec, hav.symm, hbv.symm]
            · rw [Function.update_of_ne hiv]
          rw [hupd] at hval
          have htrue := hDcomp.1 a b habG
          change (wiresFrom D.gates (List.ofFn (pairVec a b))).getD D.output false = true at htrue
          rw [htrue] at hval; cases hval
      obtain ⟨out, hout⟩ := hout_some
      have ⟨hD'mono, hD'comp⟩ := helim_v v out hout
      -- At least 1 OR gate must drop!
      have hdrop_pos : 1 ≤ ((Finset.range D.gates.length).filter (fun j =>
          let g := D.gates.getD j ⟨GateOp.and, []⟩
          g.op = GateOp.or ∧
          ((g.inputs.map fun i => (elimFPass n (D.gates.take j) (initFVar n v, [])).1.getD i none).filterMap id).length ≤ 1)).card := by
        by_contra hzero
        have hemp : ∀ j (hj : j < D.gates.length), (D.gates[j]'hj).op = GateOp.or →
            ∀ i ∈ (D.gates[j]'hj).inputs, (elimFPass n (D.gates.take j) (initFVar n v, [])).1.getD i none ≠ none := by
          intro j hj hor i hi hnone
          have hlen_le : ((D.gates[j].inputs.map fun k => (elimFPass n (D.gates.take j) (initFVar n v, [])).1.getD k none).filterMap id).length ≤ 1 := by
            have h2 := (hDmono D.gates[j] (List.getElem_mem hj)).2
            rcases hins : D.gates[j].inputs with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
            · simp
            · simp only [List.map_cons, List.map_nil]
              cases h_a : (elimFPass n (D.gates.take j) (initFVar n v, [])).1.getD a none with
              | none => change ([] : List ℕ).length ≤ 1; simp
              | some k => change [k].length ≤ 1; simp
            · rw [hins] at hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
              rcases hi with rfl | rfl
              · simp only [List.map_cons, List.map_nil, hnone, List.filterMap_cons_none]
                cases h_b : (elimFPass n (D.gates.take j) (initFVar n v, [])).1.getD b none with
                | none => change ([] : List ℕ).length ≤ 1; simp
                | some k => change [k].length ≤ 1; simp
              · simp only [List.map_cons, List.map_nil, hnone, List.filterMap_cons_none]
                cases h_a : (elimFPass n (D.gates.take j) (initFVar n v, [])).1.getD a none with
                | none => change ([] : List ℕ).length ≤ 1; simp
                | some k => change [k].length ≤ 1; simp
            · rw [hins] at h2; simp at h2
          have hmem : j ∈ (Finset.range D.gates.length).filter (fun j =>
              let g := D.gates.getD j ⟨GateOp.and, []⟩
              g.op = GateOp.or ∧
              ((g.inputs.map fun k => (elimFPass n (D.gates.take j) (initFVar n v, [])).1.getD k none).filterMap id).length ≤ 1) := by
            simp only [Finset.mem_filter, Finset.mem_range]
            refine ⟨hj, ?_⟩
            rw [List.getD_eq_getElem _ _ hj]
            exact ⟨hor, hlen_le⟩
          have hpos : 0 < _ := Finset.card_pos.2 ⟨j, hmem⟩
          omega
        -- Then every wire with acc.1.getD w ≠ none has same value on unitVec u and pairVec u v!
        have hag : ∀ w < n + D.gates.length, acc.1.getD w none ≠ none →
            (wiresFrom D.gates (List.ofFn (pairVec v u))).getD w false = true →
            (wiresFrom D.gates (List.ofFn (unitVec u))).getD w false = true := by
          intro w
          induction w using Nat.strong_induction_on with
          | ind w ihw =>
            intro hw hne hval
            by_cases hlt : w < n
            · rw [hacc, elimFPass_getD_lt _ _ _ (by simp [initFVar]; exact hlt)] at hne
              rw [initFVar, ofFn_getD_lt _ _ hlt] at hne
              have hne_v : (⟨w, hlt⟩ : Fin n) ≠ v := by intro e; rw [e] at hne; simp at hne
              rw [wiresFrom_getD_lt _ _ (by simp; exact hlt), ofFn_getD_lt _ _ hlt] at hval ⊢
              simp only [pairVec, decide_eq_true_eq] at hval
              rcases hval with h | h
              · exact absurd h hne_v
              · simp [unitVec, h]
            · have hj : w - n < D.gates.length := by omega
              have hweq : n + (w - n) = w := by omega
              set acc_j := elimFPass n (D.gates.take (w - n)) (initFVar n v, [])
              have hacc_j_len : acc_j.1.length = n + (w - n) := by
                rw [elimFPass_fst_len, show (initFVar n v).length = n by simp [initFVar], List.length_take, Nat.min_eq_left hj.le]
              have hst_w : acc.1.getD w none = (elimFStep n acc_j D.gates[w - n]).1.getD (n + (w - n)) none := by
                have hsplit : D.gates = D.gates.take (w - n) ++ D.gates[w - n] :: D.gates.drop (w - n + 1) := by simp
                conv_lhs => rw [← hweq, hacc, hsplit, elimFPass_append, elimFPass_cons]
                have hstep_len : (elimFStep n acc_j D.gates[w - n]).1.length = n + (w - n) + 1 := by
                  unfold elimFStep
                  rcases (hDmono D.gates[w - n] (List.getElem_mem hj)).1 with hop | hop
                  · rw [hop]; dsimp only; split_ifs <;> simp [hacc_j_len]
                  · rw [hop]; dsimp only; split <;> simp [hacc_j_len]
                exact elimFPass_getD_lt _ _ _ (by rw [hstep_len]; omega)
              have hin_ne : ∀ i ∈ D.gates[w - n].inputs, acc_j.1.getD i none ≠ none := by
                intro i hi hnone
                rcases (hDmono D.gates[w - n] (List.getElem_mem hj)).1 with hop | hop
                · have hany : (D.gates[w - n].inputs.map fun k => acc_j.1.getD k none).any Option.isNone = true :=
                    List.any_eq_true.2 ⟨none, List.mem_map.2 ⟨i, hi, hnone⟩, rfl⟩
                  have hwn : (elimFStep n acc_j D.gates[w - n]).1.getD (n + (w - n)) none = none := by
                    unfold elimFStep; rw [hop]; dsimp only; rw [if_pos hany, ← hacc_j_len, getD_snoc_eq]
                  exact hne (hst_w.trans hwn)
                · exact hemp (w - n) hj hop i hi hnone
              have hin_lt : ∀ i ∈ D.gates[w - n].inputs, i < n + (w - n) := by
                intro i hi
                by_contra hge; push_neg at hge
                exact hin_ne i hi (List.getD_eq_default _ _ (by omega))
              have hgd1 := wiresFrom_gate_getD D.gates (List.ofFn (pairVec v u)) hj
              have hgd2 := wiresFrom_gate_getD D.gates (List.ofFn (unitVec u)) hj
              simp only [List.length_ofFn, hweq] at hgd1 hgd2
              rw [hgd1] at hval; rw [hgd2]
              refine eval_mono_op (D.gates[w - n]).op (by simpa using (hDmono D.gates[w - n] (List.getElem_mem hj)).1) _ _ (by simp) ?_ hval
              intro k hk h1
              simp only [List.getElem_map] at h1 ⊢
              have hk' : k < D.gates[w - n].inputs.length := by simpa using hk
              set idx := D.gates[w - n].inputs[k]'hk'
              have hidx_mem : idx ∈ D.gates[w - n].inputs := List.getElem_mem hk'
              have hidx_lt : idx < n + (w - n) := hin_lt idx hidx_mem
              change (wiresFrom (D.gates.take (w - n)) (List.ofFn (pairVec v u))).getD idx false = true at h1
              change (wiresFrom (D.gates.take (w - n)) (List.ofFn (unitVec u))).getD idx false = true
              rw [wiresFrom_take_getD _ _ hj (by simp; exact hidx_lt)] at h1 ⊢
              have hidx_ne : acc.1.getD idx none ≠ none := by
                have hsplit : D.gates = D.gates.take (w - n) ++ D.gates.drop (w - n) := (List.take_append_drop _ _).symm
                rw [hacc]; conv_lhs => rw [hsplit, elimFPass_append]
                rw [elimFPass_getD_lt _ _ _ (by rw [hacc_j_len]; exact hidx_lt)]
                exact hin_ne idx hidx_mem
              exact ihw idx (by omega) (by omega) hidx_ne h1
        have hout_lt : D.output < n + D.gates.length := by
          by_contra hge; push_neg at hge
          have hlen : acc.1.length = n + D.gates.length := by
            rw [hacc, elimFPass_fst_len, show (initFVar n v).length = n by simp [initFVar]]
          rw [List.getD_eq_default _ _ (by omega)] at hout; cases hout
        have hfalse : D.eval (List.ofFn (unitVec u)) = true := hag D.output hout_lt (by rw [hout]; simp) (hDcomp.1 v u huv)
        rw [hDcomp.2.1 u] at hfalse; cases hfalse
      have hor_drop := elimFPass_orCount_add_dropped n D.gates (initFVar n v) (fun g hg => (hDmono g hg).1)
      have hIH := ih G'.edgeSet.ncard (by omega) n G' ⟨acc.2, out⟩ rfl hG'sparse hG'noC4 hD'mono hD'comp
      change orCount ⟨acc.2, out⟩ + _ = orCount D at hor_drop
      omega
    · -- CASE 2: No vertex has degree 1 -> every non-isolated vertex has degree 2!
      push_neg at hleaf
      let S : Finset (Fin n) := Finset.univ.filter (fun v => ∃ u, G.Adj v u)
      have hE_eq : {e : Sym2 (Fin n) | e ∈ G.edgeSet ∧ ∀ v ∈ e, v ∈ S} = G.edgeSet := by
        ext e
        induction e using Sym2.ind with
        | _ a b =>
          simp only [Set.mem_setOf_eq, SimpleGraph.mem_edgeSet, and_iff_left_iff_imp]
          intro hab v hv
          simp only [Sym2.mem_iff] at hv
          simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
          rcases hv with rfl | rfl
          · exact ⟨b, hab⟩
          · exact ⟨a, hab.symm⟩
      have hcard_le : G.edgeFinset.card ≤ S.card := by
        have h1 := hsparse S
        rw [hE_eq, ← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset] at h1
        exact h1
      have hdeg_ge2 : ∀ v ∈ S, 2 ≤ G.degree v := by
        intro v hv
        simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hv
        obtain ⟨u, huv⟩ := hv
        have hpos : 0 < G.degree v := by
          rw [← SimpleGraph.card_neighborFinset_eq_degree]
          exact Finset.card_pos.2 ⟨u, (SimpleGraph.mem_neighborFinset G v u).2 huv⟩
        have hne1 := hleaf v
        omega
      have hsum_deg : ∑ v ∈ S, G.degree v = 2 * G.edgeFinset.card := by
        rw [← SimpleGraph.sum_degrees_eq_twice_card_edges]
        apply Finset.sum_subset (Finset.subset_univ S)
        intro v _ hvS
        simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, not_exists] at hvS
        rw [← SimpleGraph.card_neighborFinset_eq_degree, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
        intro u hu
        exact hvS u ((SimpleGraph.mem_neighborFinset G v u).1 hu)
      have hdeg_eq2 : ∀ v ∈ S, G.degree v = 2 := by
        intro v hv
        have hle := hdeg_ge2 v hv
        by_contra hne
        have hgt : 3 ≤ G.degree v := by omega
        have hsum_ge : 2 * S.card + 1 ≤ ∑ w ∈ S, G.degree w := by
          rw [← Finset.add_sum_erase S _ hv]
          have hrest : ∑ w ∈ S.erase v, 2 ≤ ∑ w ∈ S.erase v, G.degree w :=
            Finset.sum_le_sum fun w hw => hdeg_ge2 w (Finset.mem_of_mem_erase hw)
          simp only [Finset.sum_const, smul_eq_mul] at hrest
          have hce := Finset.card_erase_add_one hv
          omega
        omega
      -- Every vertex of an edge is in S, and |E(G)| ≥ 3!
      have hE_ge3 : 3 ≤ G.edgeSet.ncard := by
        have hpos : 0 < G.edgeSet.ncard := by omega
        obtain ⟨e, he⟩ := Set.nonempty_of_ncard_ne_zero (by omega : G.edgeSet.ncard ≠ 0)
        induction e using Sym2.ind with
        | _ a b =>
          have hab : G.Adj a b := he
          have haS : a ∈ S := Finset.mem_filter.2 ⟨Finset.mem_univ _, b, hab⟩
          have hbS : b ∈ S := Finset.mem_filter.2 ⟨Finset.mem_univ _, a, hab.symm⟩
          have hda := hdeg_eq2 a haS
          have hdb := hdeg_eq2 b hbS
          have ha_n : (G.neighborFinset a).card = 2 := by simpa [SimpleGraph.card_neighborFinset_eq_degree] using hda
          have hb_n : (G.neighborFinset b).card = 2 := by simpa [SimpleGraph.card_neighborFinset_eq_degree] using hdb
          have hne_a : ((G.neighborFinset a).erase b).Nonempty := by
            rw [← Finset.card_pos, Finset.card_erase_of_mem ((SimpleGraph.mem_neighborFinset G a b).2 hab), ha_n]; omega
          obtain ⟨c, hc⟩ := hne_a
          obtain ⟨hcb, hac⟩ := Finset.mem_erase.1 hc
          have hac_adj : G.Adj a c := (SimpleGraph.mem_neighborFinset G a c).1 hac
          have hne_b : ((G.neighborFinset b).erase a).Nonempty := by
            rw [← Finset.card_pos, Finset.card_erase_of_mem ((SimpleGraph.mem_neighborFinset G b a).2 hab.symm), hb_n]; omega
          obtain ⟨d, hd⟩ := hne_b
          obtain ⟨hda', hbd⟩ := Finset.mem_erase.1 hd
          have hbd_adj : G.Adj b d := (SimpleGraph.mem_neighborFinset G b d).1 hbd
          have he1 : s(a, b) ∈ G.edgeFinset := SimpleGraph.mem_edgeFinset.2 hab
          have he2 : s(a, c) ∈ G.edgeFinset := SimpleGraph.mem_edgeFinset.2 hac_adj
          have he3 : s(b, d) ∈ G.edgeFinset := SimpleGraph.mem_edgeFinset.2 hbd_adj
          have h12 : s(a, b) ≠ s(a, c) := by
            intro h; rcases Sym2.eq_iff.1 h with ⟨_, h2⟩ | ⟨_, h2⟩
            · exact hcb h2.symm
            · rw [h2] at hab; exact G.irrefl hab
          have h13 : s(a, b) ≠ s(b, d) := by
            intro h; rcases Sym2.eq_iff.1 h with ⟨h1, _⟩ | ⟨h1, _⟩
            · rw [h1] at hab; exact G.irrefl hab
            · exact hda' h1.symm
          have h23 : s(a, c) ≠ s(b, d) := by
            intro h; rcases Sym2.eq_iff.1 h with ⟨h1, _⟩ | ⟨h1, _⟩
            · rw [h1] at hab; exact G.irrefl hab
            · exact hda' h1.symm
          have hsub : ({s(a, b), s(a, c), s(b, d)} : Finset (Sym2 (Fin n))) ⊆ G.edgeFinset := by
            intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
            rcases hx with rfl | rfl | rfl <;> assumption
          have h3 : ({s(a, b), s(a, c), s(b, d)} : Finset (Sym2 (Fin n))).card = 3 := by
            rw [Finset.card_insert_of_notMem (by simp [h12, h13]), Finset.card_pair h23]
          have hle := Finset.card_le_card hsub
          rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]
          omega
      -- D must have at least one OR gate!
      have hex_or : ∃ j : ℕ, ∃ hj : j < D.gates.length, (D.gates[j]'hj).op = GateOp.or := by
        by_contra hno; push_neg at hno
        have hall_and : ∀ j < D.gates.length, (D.gates.getD j ⟨GateOp.and, []⟩).op = GateOp.and := by
          intro j hj
          rw [List.getD_eq_getElem _ _ hj]
          rcases (hDmono D.gates[j] (List.getElem_mem hj)).1 with h | h
          · exact h
          · exact absurd h (hno j hj)
        have hch := and_initSeg_char (n := n) (gs := D.gates) (j0 := D.gates.length) le_rfl hall_and
        have htwo : ∃ a b c d : Fin n, G.Adj a b ∧ G.Adj c d ∧ s(a, b) ≠ s(c, d) := by
          have hcard2 : 2 ≤ G.edgeFinset.card := by
            rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset] at hE_ge3; omega
          obtain ⟨e1, he1, e2, he2, h12⟩ := Finset.one_lt_card.1 (by omega : 1 < G.edgeFinset.card)
          induction e1 using Sym2.ind with
          | _ a b =>
            induction e2 using Sym2.ind with
            | _ c d =>
              exact ⟨a, b, c, d, SimpleGraph.mem_edgeFinset.1 he1, SimpleGraph.mem_edgeFinset.1 he2, h12⟩
        obtain ⟨a, b, c, d, hab, hcd, hne⟩ := htwo
        by_cases hout : D.output < n + D.gates.length
        · rcases hch D.output hout with hf | ⟨T, hT⟩
          · have h1 := hDcomp.1 a b hab
            change (wiresFrom D.gates (List.ofFn (pairVec a b))).getD D.output false = true at h1
            rw [hf] at h1; cases h1
          · have h1 := (hT (pairVec a b)).1 (hDcomp.1 a b hab)
            have h2 := (hT (pairVec c d)).1 (hDcomp.1 c d hcd)
            have hTsub : ∀ k ∈ T, (k = a ∨ k = b) ∧ (k = c ∨ k = d) := fun k hk =>
              ⟨by simpa [pairVec] using h1 k hk, by simpa [pairVec] using h2 k hk⟩
            by_cases hTa : a ∈ T
            · have hTb : b ∉ T := by
                intro hTb
                have ha2 := (hTsub a hTa).2
                have hb2 := (hTsub b hTb).2
                have hab_ne : a ≠ b := fun e => G.irrefl (e ▸ hab)
                rcases ha2 with rfl | rfl <;> rcases hb2 with rfl | rfl
                · exact hab_ne rfl
                · exact hne rfl
                · exact hne Sym2.eq_swap
                · exact hab_ne rfl
              have ht := (hT (unitVec a)).2 (fun k hk => by
                rcases (hTsub k hk).1 with rfl | rfl
                · simp [unitVec]
                · exact absurd hk hTb)
              change D.eval (List.ofFn (unitVec a)) = true at ht
              rw [hDcomp.2.1 a] at ht; cases ht
            · have ht := (hT (unitVec b)).2 (fun k hk => by
                rcases (hTsub k hk).1 with rfl | rfl
                · exact absurd hk hTa
                · simp [unitVec])
              change D.eval (List.ofFn (unitVec b)) = true at ht
              rw [hDcomp.2.1 b] at ht; cases ht
        · have h1 := hDcomp.1 a b hab
          change (wiresFrom D.gates (List.ofFn (pairVec a b))).getD D.output false = true at h1
          rw [List.getD_eq_default _ _ (by rw [wiresFrom_length, List.length_ofFn]; omega)] at h1
          cases h1
      -- Pick the FIRST OR gate j0!
      let j0 := Nat.find hex_or
      obtain ⟨hj0, hj0_or⟩ := Nat.find_spec hex_or
      have hj0_first : ∀ j < j0, (D.gates.getD j ⟨GateOp.and, []⟩).op = GateOp.and := by
        intro j hj
        have hjlen : j < D.gates.length := by omega
        rw [List.getD_eq_getElem _ _ hjlen]
        have hnot := Nat.find_min hex_or hj
        rcases (hDmono D.gates[j] (List.getElem_mem hjlen)).1 with h | h
        · exact h
        · exact absurd ⟨hjlen, h⟩ hnot
      have hand_pre := and_initSeg_char (n := n) (gs := D.gates) (j0 := j0) hj0.le hj0_first
      -- Check inputs of D.gates[j0]: must be 2 in-bounds inputs [a, b]
      have hlen2 : (D.gates[j0]).inputs.length ≤ 2 := (hDmono D.gates[j0] (List.getElem_mem hj0)).2
      -- Helper: if D.gates[j0] is always false, elimFGateC contradicts minimality
      have hnot_all_false : ¬ ∀ x : Fin n → Bool, (wiresFrom D.gates (List.ofFn x)).getD (n + j0) false = false := by
        intro hf
        obtain ⟨hm', hor', hev'⟩ := elimFGateC_spec n j0 D hDmono hj0 hf
        have hcomp' : ComputesEdges G (elimFGateC n j0 D) :=
          ⟨fun u v h => by rw [hev']; exact hDcomp.1 u v h,
           fun u => by rw [hev']; exact hDcomp.2.1 u,
           fun u v h => by rw [hev']; exact hDcomp.2.2 u v h⟩
        have hle := hDmin _ hm' hcomp'
        have hor1 := hor' hj0_or
        omega
      -- Helper: if D.gates[j0] is always true, setTrueC contradicts minimality
      have hnot_all_true : ¬ ∀ x : Fin n → Bool, (wiresFrom D.gates (List.ofFn x)).getD (n + j0) false = true := by
        intro ht
        have hm' := setTrueC_mono2 j0 D hDmono
        have hor' := setTrueC_orCount j0 D hj0 hj0_or
        have hcomp' : ComputesEdges G (setTrueC j0 D) :=
          ⟨fun u v h => by rw [setTrueC_eval j0 D hj0 _ (ht _)]; exact hDcomp.1 u v h,
           fun u => by rw [setTrueC_eval j0 D hj0 _ (ht _)]; exact hDcomp.2.1 u,
           fun u v h => by rw [setTrueC_eval j0 D hj0 _ (ht _)]; exact hDcomp.2.2 u v h⟩
        have hle := hDmin _ hm' hcomp'
        omega
      -- Helper: deleting j0 replacing with w < n + j0 gives contradiction if w = n + j0 on all edges
      have hnot_eq_in : ∀ w < n + j0,
          (∀ x : Fin n → Bool, (wiresFrom D.gates (List.ofFn x)).getD w false = true →
            (wiresFrom D.gates (List.ofFn x)).getD (n + j0) false = true) →
          ¬ (∀ a b : Fin n, G.Adj a b →
            (wiresFrom D.gates (List.ofFn (pairVec a b))).getD w false =
            (wiresFrom D.gates (List.ofFn (pairVec a b))).getD (n + j0) false) := by
        intro w hw hle heq_e
        have hm' := rdelC_mono2 n j0 w D hDmono
        have hor' := rdelC_orCount n j0 w D hj0 hj0_or
        have hcomp' : ComputesEdges G (rdelC n j0 w D) := by
          refine ⟨?_, ?_, ?_⟩
          · intro a b hab
            rw [rdelC_eval_eq hj0 hw _ (heq_e a b hab)]
            exact hDcomp.1 a b hab
          · intro a
            apply Bool.eq_false_iff.2; intro h
            have h1 := rdelC_eval_le hDmono hj0 hw _ (hle _) h
            rw [hDcomp.2.1 a] at h1; cases h1
          · intro a b hnot
            apply Bool.eq_false_iff.2; intro h
            have h1 := rdelC_eval_le hDmono hj0 hw _ (hle _) h
            rw [hDcomp.2.2 a b hnot] at h1; cases h1
        have hmin' := hDmin _ hm' hcomp'
        omega
      -- Helper: gate j0 evaluation
      have hj0_val : ∀ x : Fin n → Bool,
          (wiresFrom D.gates (List.ofFn x)).getD (n + j0) false =
            (D.gates[j0].inputs.map fun i => if i < n + j0 then (wiresFrom D.gates (List.ofFn x)).getD i false else false).any id := by
        intro x
        have h1 := wiresFrom_gate_getD D.gates (List.ofFn x) hj0
        simp only [List.length_ofFn, hj0_or, GateOp.eval] at h1
        rw [h1]; congr 1; apply List.map_congr_left; intro i _
        split_ifs with hi
        · exact wiresFrom_take_getD _ _ hj0 (by simp; exact hi)
        · exact List.getD_eq_default _ _ (by rw [wiresFrom_length, List.length_ofFn, List.length_take, Nat.min_eq_left hj0.le]; omega)
      -- Deduce D.gates[j0].inputs = [w1, w2] with w1 < n + j0, w2 < n + j0
      have hinputs_two : ∃ w1 w2 : ℕ, D.gates[j0].inputs = [w1, w2] ∧ w1 < n + j0 ∧ w2 < n + j0 := by
        rcases hins : D.gates[j0].inputs with _ | ⟨w1, _ | ⟨w2, _ | _⟩⟩
        · exfalso; apply hnot_all_false; intro x; rw [hj0_val, hins]; rfl
        · exfalso
          by_cases hw1 : w1 < n + j0
          · apply hnot_eq_in w1 hw1
            · intro x h; rw [hj0_val, hins]; simp only [List.map_cons, List.map_nil, hw1, ↓reduceIte, List.any_cons, List.any_nil, id_eq, Bool.or_false]; exact h
            · intro a b _; rw [hj0_val, hins]; simp only [List.map_cons, List.map_nil, hw1, ↓reduceIte, List.any_cons, List.any_nil, id_eq, Bool.or_false]
          · apply hnot_all_false; intro x; rw [hj0_val, hins]; simp only [List.map_cons, List.map_nil, hw1, ↓reduceIte, List.any_cons, List.any_nil, id_eq, Bool.or_false]
        · by_cases hw1 : w1 < n + j0
          · by_cases hw2 : w2 < n + j0
            · exact ⟨w1, w2, rfl, hw1, hw2⟩
            · exfalso; apply hnot_eq_in w1 hw1
              · intro x h; rw [hj0_val, hins]; simp only [List.map_cons, List.map_nil, hw1, hw2, ↓reduceIte, List.any_cons, List.any_nil, id_eq, Bool.or_false]; exact h
              · intro a b _; rw [hj0_val, hins]; simp only [List.map_cons, List.map_nil, hw1, hw2, ↓reduceIte, List.any_cons, List.any_nil, id_eq, Bool.or_false]
          · by_cases hw2 : w2 < n + j0
            · exfalso; apply hnot_eq_in w2 hw2
              · intro x h; rw [hj0_val, hins]; simp only [List.map_cons, List.map_nil, hw1, hw2, ↓reduceIte, List.any_cons, List.any_nil, id_eq, Bool.or_false, Bool.false_or]; exact h
              · intro a b _; rw [hj0_val, hins]; simp only [List.map_cons, List.map_nil, hw1, hw2, ↓reduceIte, List.any_cons, List.any_nil, id_eq, Bool.or_false, Bool.false_or]
            · exfalso; apply hnot_all_false; intro x; rw [hj0_val, hins]; simp only [List.map_cons, List.map_nil, hw1, hw2, ↓reduceIte, List.any_cons, List.any_nil, id_eq, Bool.or_false]
        · rw [hins] at hlen2; simp at hlen2
      obtain ⟨w1, w2, hins_eq, hw1_lt, hw2_lt⟩ := hinputs_two
      have hj0_or_val : ∀ x : Fin n → Bool,
          (wiresFrom D.gates (List.ofFn x)).getD (n + j0) false =
            ((wiresFrom D.gates (List.ofFn x)).getD w1 false || (wiresFrom D.gates (List.ofFn x)).getD w2 false) := by
        intro x; rw [hj0_val, hins_eq]; simp [hw1_lt, hw2_lt, id_eq]
      -- Neither w1 nor w2 can be identically false, so both have sets S1, S2
      have hS1_ex : ∃ S1 : Finset (Fin n), S1.Nonempty ∧ ∀ x : Fin n → Bool,
          (wiresFrom D.gates (List.ofFn x)).getD w1 false = true ↔ ∀ i ∈ S1, x i = true := by
        rcases hand_pre w1 hw1_lt with hf | ⟨S1, hS1⟩
        · exfalso; apply hnot_eq_in w2 hw2_lt
          · intro x h; rw [hj0_or_val, h, Bool.or_true]
          · intro a b _; rw [hj0_or_val, hf, Bool.false_or]
        · by_cases hne : S1.Nonempty
          · exact ⟨S1, hne, hS1⟩
          · exfalso; rw [Finset.not_nonempty_iff_eq_empty] at hne; subst hne
            apply hnot_all_true; intro x
            rw [hj0_or_val, (hS1 x).2 (by simp), Bool.true_or]
      have hS2_ex : ∃ S2 : Finset (Fin n), S2.Nonempty ∧ ∀ x : Fin n → Bool,
          (wiresFrom D.gates (List.ofFn x)).getD w2 false = true ↔ ∀ i ∈ S2, x i = true := by
        rcases hand_pre w2 hw2_lt with hf | ⟨S2, hS2⟩
        · exfalso; apply hnot_eq_in w1 hw1_lt
          · intro x h; rw [hj0_or_val, h, Bool.true_or]
          · intro a b _; rw [hj0_or_val, hf, Bool.or_false]
        · by_cases hne : S2.Nonempty
          · exact ⟨S2, hne, hS2⟩
          · exfalso; rw [Finset.not_nonempty_iff_eq_empty] at hne; subst hne
            apply hnot_all_true; intro x
            rw [hj0_or_val, (hS2 x).2 (by simp), Bool.or_true]
      obtain ⟨S1, hS1_ne, hS1⟩ := hS1_ex
      obtain ⟨S2, hS2_ne, hS2⟩ := hS2_ex
      -- Helper: if some input wi (w_other) has |Si| ≥ 2, then either contradiction or edge deletion finishes!
      have hcard_ge2_done : ∀ (wi w_other : ℕ) (Si : Finset (Fin n)),
          (wi = w1 ∧ w_other = w2 ∨ wi = w2 ∧ w_other = w1) →
          w_other < n + j0 →
          (∀ x : Fin n → Bool, (wiresFrom D.gates (List.ofFn x)).getD wi false = true ↔ ∀ k ∈ Si, x k = true) →
          2 ≤ Si.card →
          G.edgeSet.ncard ≤ orCount D + 1 := by
        intro wi w_other Si hpair hwo_lt hSi hSi2
        have hle_other : ∀ x : Fin n → Bool, (wiresFrom D.gates (List.ofFn x)).getD w_other false = true →
            (wiresFrom D.gates (List.ofFn x)).getD (n + j0) false = true := by
          intro x h; rw [hj0_or_val]; rcases hpair with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h2] at h <;> rw [h] <;> simp
        by_cases hSi_edge : ∃ a b : Fin n, G.Adj a b ∧ Si = {a, b}
        · obtain ⟨a, b, hab, rfl⟩ := hSi_edge
          -- Delete edge s(a, b) from G and replace j0 by w_other!
          let G' : SimpleGraph (Fin n) := SimpleGraph.fromRel (fun p q => G.Adj p q ∧ s(p, q) ≠ s(a, b))
          have hG'adj : ∀ p q, G'.Adj p q ↔ G.Adj p q ∧ s(p, q) ≠ s(a, b) := by
            intro p q; simp only [G', SimpleGraph.fromRel_adj]
            constructor
            · rintro ⟨_, (⟨h, hne⟩ | ⟨h, hne⟩)⟩
              · exact ⟨h, hne⟩
              · exact ⟨h.symm, by rwa [Sym2.eq_swap] at hne⟩
            · rintro ⟨h, hne⟩
              exact ⟨fun e => G.irrefl (e ▸ h), Or.inl ⟨h, hne⟩⟩
          have hE' : G'.edgeSet = G.edgeSet \ {s(a, b)} := by
            ext e; induction e using Sym2.ind with
            | _ p q => rw [Set.mem_diff, Set.mem_singleton_iff, SimpleGraph.mem_edgeSet, SimpleGraph.mem_edgeSet, hG'adj]
          have hcard_G' : G'.edgeSet.ncard + 1 = G.edgeSet.ncard := by
            rw [hE', Set.ncard_diff_singleton_of_mem ((SimpleGraph.mem_edgeSet G).2 hab)]; omega
          have hG'sparse : ∀ T : Finset (Fin n),
              {e : Sym2 (Fin n) | e ∈ G'.edgeSet ∧ ∀ u ∈ e, u ∈ T}.ncard ≤ T.card := by
            intro T
            have hsub : {e : Sym2 (Fin n) | e ∈ G'.edgeSet ∧ ∀ u ∈ e, u ∈ T} ⊆
                {e : Sym2 (Fin n) | e ∈ G.edgeSet ∧ ∀ u ∈ e, u ∈ T} :=
              fun e ⟨he, hT⟩ => ⟨by rw [hE'] at he; exact he.1, hT⟩
            exact (Set.ncard_le_ncard hsub (Set.toFinite _)).trans (hsparse T)
          have hG'noC4 : ∀ (w : Fin n) (c : G'.Walk w w), c.IsCycle → c.length ≠ 4 := by
            intro w c hc
            have hhom : G' ≤ G := fun p q hpq => ((hG'adj p q).1 hpq).1
            have hc' := hc.map (f := SimpleGraph.Hom.ofLE hhom) Function.injective_id
            rw [← SimpleGraph.Walk.length_map (SimpleGraph.Hom.ofLE hhom) c]
            exact hnoC4 w _ hc'
          let D' := rdelC n j0 w_other D
          have hD'mono : Monotone2 D' := rdelC_mono2 n j0 w_other D hDmono
          have hD'or : orCount D' + 1 = orCount D := rdelC_orCount n j0 w_other D hj0 hj0_or
          -- For every edge p-q of G', wi evaluates to false on pairVec p q
          have hD'_edges : ∀ p q, G'.Adj p q → D'.eval (List.ofFn (pairVec p q)) = true := by
            intro p q hpq
            have ⟨hpqG, hne_ab⟩ := (hG'adj p q).1 hpq
            have hwi_f : (wiresFrom D.gates (List.ofFn (pairVec p q))).getD wi false = false := by
              apply Bool.eq_false_iff.2; intro ht
              have h1 := (hSi (pairVec p q)).1 ht
              have ha' : a = p ∨ a = q := by simpa [pairVec] using h1 a (by simp)
              have hb' : b = p ∨ b = q := by simpa [pairVec] using h1 b (by simp)
              have hab_ne : a ≠ b := fun e => G.irrefl (e ▸ hab)
              rcases ha' with rfl | rfl <;> rcases hb' with rfl | rfl
              · exact hab_ne rfl
              · exact hne_ab rfl
              · exact hne_ab Sym2.eq_swap
              · exact hab_ne rfl
            have heq_j0 : (wiresFrom D.gates (List.ofFn (pairVec p q))).getD w_other false =
                (wiresFrom D.gates (List.ofFn (pairVec p q))).getD (n + j0) false := by
              rw [hj0_or_val]
              rcases hpair with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1] at hwi_f <;> rw [h2, hwi_f] <;> simp
            rw [rdelC_eval_eq hj0 hwo_lt _ heq_j0]
            exact hDcomp.1 p q hpqG
          -- D' cannot be true on pairVec a b (else D' computes G with fewer ORs!)
          have hD'_ab_false : D'.eval (List.ofFn (pairVec a b)) = false := by
            apply Bool.eq_false_iff.2; intro hab_t
            have hcomp_G : ComputesEdges G D' := by
              refine ⟨?_, ?_, ?_⟩
              · intro p q hpq
                by_cases he : s(p, q) = s(a, b)
                · rcases Sym2.eq_iff.1 he with ⟨h1, h2⟩ | ⟨h1, h2⟩
                  · rw [h1, h2]; exact hab_t
                  · have hsym : pairVec b a = pairVec a b := by funext i; simp [pairVec, or_comm]
                    rw [h1, h2, hsym]; exact hab_t
                · exact hD'_edges p q ((hG'adj p q).2 ⟨hpq, he⟩)
              · intro u
                apply Bool.eq_false_iff.2; intro h
                have h1 := rdelC_eval_le hDmono hj0 hwo_lt _ (hle_other _) h
                rw [hDcomp.2.1 u] at h1; cases h1
              · intro p q hnot
                apply Bool.eq_false_iff.2; intro h
                have h1 := rdelC_eval_le hDmono hj0 hwo_lt _ (hle_other _) h
                rw [hDcomp.2.2 p q hnot] at h1; cases h1
            have hle := hDmin D' hD'mono hcomp_G
            omega
          have hD'comp : ComputesEdges G' D' := by
            refine ⟨hD'_edges, ?_, ?_⟩
            · intro u
              apply Bool.eq_false_iff.2; intro h
              have h1 := rdelC_eval_le hDmono hj0 hwo_lt _ (hle_other _) h
              rw [hDcomp.2.1 u] at h1; cases h1
            · intro p q hnot
              by_cases hpqG : G.Adj p q
              · have he : s(p, q) = s(a, b) := by
                  by_contra hne; exact hnot ((hG'adj p q).2 ⟨hpqG, hne⟩)
                rcases Sym2.eq_iff.1 he with ⟨h1, h2⟩ | ⟨h1, h2⟩
                · rw [h1, h2]; exact hD'_ab_false
                · have hsym : pairVec b a = pairVec a b := by funext i; simp [pairVec, or_comm]
                  rw [h1, h2, hsym]; exact hD'_ab_false
              · apply Bool.eq_false_iff.2; intro h
                have h1 := rdelC_eval_le hDmono hj0 hwo_lt _ (hle_other _) h
                rw [hDcomp.2.2 p q hpqG] at h1; cases h1
          have hIH := ih G'.edgeSet.ncard (by omega) n G' D' rfl hG'sparse hG'noC4 hD'mono hD'comp
          omega
        · -- Not an edge: wi evaluates to false on EVERY edge! Contradicts hDmin!
          exfalso
          apply hnot_eq_in w_other hwo_lt hle_other
          intro p q hpq
          have hwi_f : (wiresFrom D.gates (List.ofFn (pairVec p q))).getD wi false = false := by
            apply Bool.eq_false_iff.2; intro ht
            have h1 := (hSi (pairVec p q)).1 ht
            have hsub : Si ⊆ {p, q} := by
              intro k hk; have := h1 k hk; simpa [pairVec] using this
            have hle_c := Finset.card_le_card hsub
            have hpq_ne : p ≠ q := fun e => G.irrefl (e ▸ hpq)
            have hpair_c : ({p, q} : Finset (Fin n)).card = 2 := Finset.card_pair hpq_ne
            have heq_set : Si = {p, q} := Finset.eq_of_subset_of_card_le hsub (by omega)
            exact hSi_edge ⟨p, q, hpq, heq_set⟩
          rw [hj0_or_val]
          rcases hpair with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1] at hwi_f <;> rw [h2, hwi_f] <;> simp
      by_cases h1ge2 : 2 ≤ S1.card
      · exact hcard_ge2_done w1 w2 S1 (Or.inl ⟨rfl, rfl⟩) hw2_lt hS1 h1ge2
      · by_cases h2ge2 : 2 ≤ S2.card
        · exact hcard_ge2_done w2 w1 S2 (Or.inr ⟨rfl, rfl⟩) hw1_lt hS2 h2ge2
        · -- Both S1 and S2 are singletons: S1 = {u}, S2 = {v}!
          have h1eq1 : S1.card = 1 := by have := hS1_ne.card_pos; omega
          have h2eq1 : S2.card = 1 := by have := hS2_ne.card_pos; omega
          obtain ⟨u, rfl⟩ := Finset.card_eq_one.1 h1eq1
          obtain ⟨v, rfl⟩ := Finset.card_eq_one.1 h2eq1
          have huv_ne : u ≠ v := by
            intro heq; subst heq
            apply hnot_eq_in w2 hw2_lt
            · intro x h; rw [hj0_or_val, h, Bool.or_true]
            · intro a b _
              have h12 : (wiresFrom D.gates (List.ofFn (pairVec a b))).getD w1 false =
                  (wiresFrom D.gates (List.ofFn (pairVec a b))).getD w2 false := by
                apply Bool.eq_iff_iff.2
                rw [hS1, hS2]
              rw [hj0_or_val, h12, Bool.or_self]
          -- Helper: under elimFPass at x_u = false, w1 gets none, w2 gets some, so j0 drops!
          have hacc_u_j0 :
              let acc_j0 := elimFPass n (D.gates.take j0) (initFVar n u, [])
              acc_j0.1.getD w1 none = none ∧ acc_j0.1.getD w2 none ≠ none := by
            intro acc_j0
            have hinv_u : ∀ x : Fin n → Bool,
                ElimFInv n (List.ofFn x) (wiresFrom (D.gates.take j0) (List.ofFn (Function.update x u false))) acc_j0 :=
              fun x => elimFInv_pass n (List.ofFn x) (D.gates.take j0) _ (initFVar n u, [])
                (fun g hg => (hDmono g (List.mem_of_mem_take hg)).1) (elimFInv_initFVar n u x)
            have h_w2 : acc_j0.1.getD w2 none ≠ none := by
              intro hnone
              have hval := ((hinv_u (unitVec v)).2.2 w2).2
              rw [hnone] at hval
              rw [wiresFrom_take_getD _ _ hj0 (by simp; exact hw2_lt)] at hval
              have ht : (wiresFrom D.gates (List.ofFn (Function.update (unitVec v) u false))).getD w2 false = true := by
                apply (hS2 _).2; simp [Function.update_of_ne huv_ne.symm, unitVec]
              rw [ht] at hval; cases hval
            have h_w1 : acc_j0.1.getD w1 none = none := by
              -- Prove by induction on w < n + j0: if acc_j0.1.getD w none ≠ none, then value on (fun _ => true)[u := false] is true?
              -- Actually even easier: on x = fun _ => true, w1(x[u:=false]) = false, whereas ANY wire < n + j0 with acc_j0 ≠ none evaluates to true on x = fun _ => true!
              suffices htrue_all : ∀ w < n + j0, acc_j0.1.getD w none ≠ none →
                  (wiresFrom D.gates (List.ofFn (Function.update (fun _ : Fin n => true) u false))).getD w false = true by
                by_contra hne
                have ht := htrue_all w1 hw1_lt hne
                have h1 := (hS1 _).1 ht u (by simp)
                simp at h1
              intro w
              induction w using Nat.strong_induction_on with
              | ind w ihw =>
                intro hw hne
                by_cases hlt : w < n
                · rw [elimFPass_getD_lt _ _ _ (by simp [initFVar]; exact hlt)] at hne
                  rw [initFVar, ofFn_getD_lt _ _ hlt] at hne
                  have hne_u : (⟨w, hlt⟩ : Fin n) ≠ u := by intro e; rw [e] at hne; simp at hne
                  rw [wiresFrom_getD_lt _ _ (by simp; exact hlt), ofFn_getD_lt _ _ hlt,
                      Function.update_of_ne hne_u]
                · have hj : w - n < j0 := by omega
                  have hjlen : w - n < D.gates.length := by omega
                  have hweq : n + (w - n) = w := by omega
                  have hop : (D.gates[w - n]).op = GateOp.and := by
                    have := hj0_first (w - n) hj; rwa [List.getD_eq_getElem _ _ hjlen] at this
                  set acc_j := elimFPass n (D.gates.take (w - n)) (initFVar n u, [])
                  have hacc_j_len : acc_j.1.length = n + (w - n) := by
                    rw [elimFPass_fst_len, show (initFVar n u).length = n by simp [initFVar], List.length_take, Nat.min_eq_left hjlen.le]
                  have hsplit : D.gates.take j0 = D.gates.take (w - n) ++ D.gates[w - n] :: (D.gates.take j0).drop (w - n + 1) := by
                    have h1 := (List.take_append_drop (w - n) (D.gates.take j0)).symm
                    rw [List.take_take, Nat.min_eq_left hj.le, List.drop_eq_getElem_cons (by rw [List.length_take]; omega), List.getElem_take] at h1
                    exact h1
                  have hst_w : acc_j0.1.getD w none = (elimFStep n acc_j D.gates[w - n]).1.getD (n + (w - n)) none := by
                    conv_lhs => rw [← hweq]
                    show (elimFPass n (D.gates.take j0) _).1.getD _ _ = _
                    rw [hsplit, elimFPass_append, elimFPass_cons]
                    have hstep_len : (elimFStep n acc_j D.gates[w - n]).1.length = n + (w - n) + 1 := by
                      unfold elimFStep; rw [hop]; dsimp only; split_ifs <;> simp [hacc_j_len]
                    exact elimFPass_getD_lt _ _ _ (by rw [hstep_len]; omega)
                  have hin_ne : ∀ i ∈ D.gates[w - n].inputs, acc_j.1.getD i none ≠ none := by
                    intro i hi hnone
                    have hany : (D.gates[w - n].inputs.map fun k => acc_j.1.getD k none).any Option.isNone = true :=
                      List.any_eq_true.2 ⟨none, List.mem_map.2 ⟨i, hi, hnone⟩, rfl⟩
                    have hwn : (elimFStep n acc_j D.gates[w - n]).1.getD (n + (w - n)) none = none := by
                      unfold elimFStep; rw [hop]; dsimp only; rw [if_pos hany, ← hacc_j_len, getD_snoc_eq]
                    exact hne (hst_w.trans hwn)
                  have hgd := wiresFrom_gate_getD D.gates (List.ofFn (Function.update (fun _ : Fin n => true) u false)) hjlen
                  simp only [List.length_ofFn, hweq, hop] at hgd
                  rw [hgd]
                  simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq, forall_exists_index, and_imp,
                    forall_apply_eq_imp_iff₂]
                  intro i hi
                  have hilt : i < n + (w - n) := by
                    by_contra hge; push_neg at hge
                    exact hin_ne i hi (List.getD_eq_default _ _ (by omega))
                  rw [wiresFrom_take_getD _ _ hjlen (by simp; exact hilt)]
                  have hi_ne0 : acc_j0.1.getD i none ≠ none := by
                    have hsp2 : D.gates.take j0 = D.gates.take (w - n) ++ (D.gates.take j0).drop (w - n) := by
                      have h1 := (List.take_append_drop (w - n) (D.gates.take j0)).symm
                      rwa [List.take_take, Nat.min_eq_left hj.le] at h1
                    show (elimFPass n (D.gates.take j0) _).1.getD i none ≠ none
                    rw [hsp2, elimFPass_append, elimFPass_getD_lt _ _ _ (by rw [hacc_j_len]; exact hilt)]
                    exact hin_ne i hi
                  exact ihw i (by omega) (by omega) hi_ne0
            exact ⟨h_w1, h_w2⟩
          -- Now run elimFPass at x_u = false!
          set acc := elimFPass n D.gates (initFVar n u, []) with hacc
          have hj0_dropped : j0 ∈ (Finset.range D.gates.length).filter (fun j =>
              let g := D.gates.getD j ⟨GateOp.and, []⟩
              g.op = GateOp.or ∧
              ((g.inputs.map fun i => (elimFPass n (D.gates.take j) (initFVar n u, [])).1.getD i none).filterMap id).length ≤ 1) := by
            simp only [Finset.mem_filter, Finset.mem_range]
            refine ⟨hj0, ?_⟩
            rw [List.getD_eq_getElem _ _ hj0]
            refine ⟨hj0_or, ?_⟩
            rw [hins_eq]
            simp only [List.map_cons, List.map_nil, hacc_u_j0.1, List.filterMap_cons_none]
            cases h_w2 : (elimFPass n (D.gates.take j0) (initFVar n u, [])).1.getD w2 none with
            | none => change ([] : List ℕ).length ≤ 1; simp
            | some k => change [k].length ≤ 1; simp
          -- Can u be isolated in G? If so, G - u = G and j0 dropped -> contradicts hDmin!
          have hu_in_S : u ∈ S := by
            by_contra huS
            have hu_iso : ∀ w, ¬ G.Adj u w := by
              intro w huw; exact huS (Finset.mem_filter.2 ⟨Finset.mem_univ _, w, huw⟩)
            have hG_eq : SimpleGraph.fromRel (fun a b => G.Adj a b ∧ a ≠ u ∧ b ≠ u) = G := by
              ext a b; rw [(hdel_vertex u).1]
              exact ⟨fun h => h.1, fun h => ⟨h, fun e => hu_iso b (e ▸ h), fun e => hu_iso a (e ▸ h.symm)⟩⟩
            -- Output cannot be none since G has edges
            have hout_some : ∃ out, acc.1.getD D.output none = some out := by
              cases hst : acc.1.getD D.output none with
              | some out => exact ⟨out, rfl⟩
              | none =>
                exfalso
                obtain ⟨e, he⟩ := Set.nonempty_of_ncard_ne_zero (by omega : G.edgeSet.ncard ≠ 0)
                induction e using Sym2.ind with
                | _ a b =>
                  have hau : a ≠ u := fun h => hu_iso b (h ▸ he)
                  have hbu : b ≠ u := fun h => hu_iso a (h ▸ he.symm)
                  have hinv := elimFInv_pass n (List.ofFn (pairVec a b)) D.gates _ (initFVar n u, [])
                    (fun g hg => (hDmono g hg).1) (elimFInv_initFVar n u (pairVec a b))
                  have hval := (hinv.2.2 D.output).2
                  rw [← hacc, hst] at hval
                  have hupd : Function.update (pairVec a b) u false = pairVec a b := by
                    funext i; by_cases hiu : i = u
                    · subst hiu; simp [pairVec, hau.symm, hbu.symm]
                    · rw [Function.update_of_ne hiu]
                  rw [hupd] at hval
                  have ht := hDcomp.1 a b he
                  change (wiresFrom D.gates (List.ofFn (pairVec a b))).getD D.output false = true at ht
                  rw [ht] at hval; cases hval
            obtain ⟨out, hout⟩ := hout_some
            have ⟨hD'mono, hD'comp⟩ := helim_v u out hout
            rw [hG_eq] at hD'comp
            have hor_drop := elimFPass_orCount_add_dropped n D.gates (initFVar n u) (fun g hg => (hDmono g hg).1)
            have hpos : 1 ≤ _ := Finset.card_pos.2 ⟨j0, hj0_dropped⟩
            have hle := hDmin ⟨acc.2, out⟩ hD'mono hD'comp
            change orCount ⟨acc.2, out⟩ + _ = orCount D at hor_drop
            omega
          -- So deg(u) = 2! Let r1 ≠ r2 be the two neighbors of u
          have hdegu : G.degree u = 2 := hdeg_eq2 u hu_in_S
          have hnu : (G.neighborFinset u).card = 2 := by simpa [SimpleGraph.card_neighborFinset_eq_degree] using hdegu
          obtain ⟨r1, hr1m, r2, hr2m, hr12⟩ := Finset.one_lt_card.1 (by omega : 1 < (G.neighborFinset u).card)
          have hur1 : G.Adj u r1 := (SimpleGraph.mem_neighborFinset G u r1).1 hr1m
          have hur2 : G.Adj u r2 := (SimpleGraph.mem_neighborFinset G u r2).1 hr2m
          have hnu_eq : G.neighborFinset u = {r1, r2} := by
            symm; apply Finset.eq_of_subset_of_card_le
            · intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
              rcases hx with rfl | rfl <;> assumption
            · rw [Finset.card_pair hr12, hnu]
          -- G' = G - u has |E(G')| = |E(G)| - 2 ≥ 1!
          let G' : SimpleGraph (Fin n) := SimpleGraph.fromRel (fun a b => G.Adj a b ∧ a ≠ u ∧ b ≠ u)
          have ⟨hG'adj, hG'sparse, hG'noC4⟩ := hdel_vertex u
          have hE' : G'.edgeSet = (G.edgeSet \ {s(u, r1)}) \ {s(u, r2)} := by
            ext e; induction e using Sym2.ind with
            | _ a b =>
              simp only [Set.mem_diff, Set.mem_singleton_iff, SimpleGraph.mem_edgeSet]
              rw [hG'adj]
              constructor
              · rintro ⟨hab, hau, hbu⟩
                refine ⟨⟨hab, fun h => ?_⟩, fun h => ?_⟩
                · rcases Sym2.eq_iff.1 h with ⟨rfl, _⟩ | ⟨_, rfl⟩
                  · exact hau rfl
                  · exact hbu rfl
                · rcases Sym2.eq_iff.1 h with ⟨rfl, _⟩ | ⟨_, rfl⟩
                  · exact hau rfl
                  · exact hbu rfl
              · rintro ⟨⟨hab, h1⟩, h2⟩
                refine ⟨hab, ?_, ?_⟩
                · intro hau; subst a
                  have hb : b ∈ G.neighborFinset u := (SimpleGraph.mem_neighborFinset G u b).2 hab
                  rw [hnu_eq, Finset.mem_insert, Finset.mem_singleton] at hb
                  rcases hb with rfl | rfl
                  · exact h1 rfl
                  · exact h2 rfl
                · intro hbu; subst b
                  have ha : a ∈ G.neighborFinset u := (SimpleGraph.mem_neighborFinset G u a).2 hab.symm
                  rw [hnu_eq, Finset.mem_insert, Finset.mem_singleton] at ha
                  rcases ha with rfl | rfl
                  · exact h1 Sym2.eq_swap
                  · exact h2 Sym2.eq_swap
          have hne_edges : s(u, r2) ≠ s(u, r1) := by
            intro h; rcases Sym2.eq_iff.1 h with ⟨_, h2⟩ | ⟨_, h2⟩
            · exact hr12 h2.symm
            · rw [h2] at hur2; exact G.irrefl hur2
          have hcard_G' : G'.edgeSet.ncard + 2 = G.edgeSet.ncard := by
            have hr2_in : s(u, r2) ∈ G.edgeSet \ {s(u, r1)} := ⟨hur2, hne_edges⟩
            rw [hE', Set.ncard_diff_singleton_of_mem hr2_in,
                Set.ncard_diff_singleton_of_mem ((SimpleGraph.mem_edgeSet G).2 hur1)]
            omega
          have hG'_nonempty : ∃ a b : Fin n, G'.Adj a b := by
            obtain ⟨e, he⟩ := Set.nonempty_of_ncard_ne_zero (by omega : G'.edgeSet.ncard ≠ 0)
            induction e using Sym2.ind with
            | _ a b => exact ⟨a, b, he⟩
          have hout_some : ∃ out, acc.1.getD D.output none = some out := by
            cases hst : acc.1.getD D.output none with
            | some out => exact ⟨out, rfl⟩
            | none =>
              exfalso
              obtain ⟨a, b, hab⟩ := hG'_nonempty
              have ⟨habG, hau, hbu⟩ := (hG'adj a b).1 hab
              have hinv := elimFInv_pass n (List.ofFn (pairVec a b)) D.gates _ (initFVar n u, [])
                (fun g hg => (hDmono g hg).1) (elimFInv_initFVar n u (pairVec a b))
              have hval := (hinv.2.2 D.output).2
              rw [← hacc, hst] at hval
              have hupd : Function.update (pairVec a b) u false = pairVec a b := by
                funext i; by_cases hiu : i = u
                · subst hiu; simp [pairVec, hau.symm, hbu.symm]
                · rw [Function.update_of_ne hiu]
              rw [hupd] at hval
              have ht := hDcomp.1 a b habG
              change (wiresFrom D.gates (List.ofFn (pairVec a b))).getD D.output false = true at ht
              rw [ht] at hval; cases hval
          obtain ⟨out, hout⟩ := hout_some
          have ⟨hD'mono, hD'comp⟩ := helim_v u out hout
          -- Must drop at least 2 OR gates!
          let dropSet := (Finset.range D.gates.length).filter (fun j =>
              let g := D.gates.getD j ⟨GateOp.and, []⟩
              g.op = GateOp.or ∧
              ((g.inputs.map fun i => (elimFPass n (D.gates.take j) (initFVar n u, [])).1.getD i none).filterMap id).length ≤ 1)
          have hdrop2 : 2 ≤ dropSet.card := by
            by_contra hlt2
            -- Then NO OR gate j ≠ j0 drops!
            have hno_other : ∀ j (hj : j < D.gates.length), j ≠ j0 → (D.gates[j]'hj).op = GateOp.or →
                ∀ i ∈ (D.gates[j]'hj).inputs, (elimFPass n (D.gates.take j) (initFVar n u, [])).1.getD i none ≠ none := by
              intro j hj hne hor i hi hnone
              have hlen_le : ((D.gates[j].inputs.map fun k => (elimFPass n (D.gates.take j) (initFVar n u, [])).1.getD k none).filterMap id).length ≤ 1 := by
                have h2 := (hDmono D.gates[j] (List.getElem_mem hj)).2
                rcases hins : D.gates[j].inputs with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
                · simp
                · simp only [List.map_cons, List.map_nil]
                  cases h_a : (elimFPass n (D.gates.take j) (initFVar n u, [])).1.getD a none with
                | none => change ([] : List ℕ).length ≤ 1; simp
                | some k => change [k].length ≤ 1; simp
                · rw [hins] at hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
                  rcases hi with rfl | rfl
                  · simp only [List.map_cons, List.map_nil, hnone, List.filterMap_cons_none]
                    cases h_b : (elimFPass n (D.gates.take j) (initFVar n u, [])).1.getD b none with
                | none => change ([] : List ℕ).length ≤ 1; simp
                | some k => change [k].length ≤ 1; simp
                  · simp only [List.map_cons, List.map_nil, hnone, List.filterMap_cons_none]
                    cases h_a : (elimFPass n (D.gates.take j) (initFVar n u, [])).1.getD a none with
                | none => change ([] : List ℕ).length ≤ 1; simp
                | some k => change [k].length ≤ 1; simp
                · rw [hins] at h2; simp at h2
              have hmem : j ∈ dropSet := by
                simp only [dropSet, Finset.mem_filter, Finset.mem_range]
                refine ⟨hj, ?_⟩
                rw [List.getD_eq_getElem _ _ hj]
                exact ⟨hor, hlen_le⟩
              have hsub : ({j, j0} : Finset ℕ) ⊆ dropSet := by
                intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
                rcases hx with rfl | rfl <;> assumption
              have h2 := Finset.card_le_card hsub
              rw [Finset.card_pair hne] at h2
              omega
            -- Comparison claim: for any x, y with (∀ i ≠ u, x i = true → y i = true) and y v = true,
            -- every wire w with acc.1.getD w ≠ none has val(w, x) = true → val(w, y) = true!
            have hcmp : ∀ (x y : Fin n → Bool), (∀ i : Fin n, i ≠ u → x i = true → y i = true) → y v = true →
                ∀ w < n + D.gates.length, acc.1.getD w none ≠ none →
                (wiresFrom D.gates (List.ofFn x)).getD w false = true →
                (wiresFrom D.gates (List.ofFn y)).getD w false = true := by
              intro x y hxy hyv w
              induction w using Nat.strong_induction_on with
              | ind w ihw =>
                intro hw hne hval
                by_cases hlt : w < n
                · rw [hacc, elimFPass_getD_lt _ _ _ (by simp [initFVar]; exact hlt)] at hne
                  rw [initFVar, ofFn_getD_lt _ _ hlt] at hne
                  have hne_u : (⟨w, hlt⟩ : Fin n) ≠ u := by intro e; rw [e] at hne; simp at hne
                  rw [wiresFrom_getD_lt _ _ (by simp; exact hlt), ofFn_getD_lt _ _ hlt] at hval ⊢
                  exact hxy ⟨w, hlt⟩ hne_u hval
                · have hj : w - n < D.gates.length := by omega
                  have hweq : n + (w - n) = w := by omega
                  by_cases hjeq : w - n = j0
                  · rw [← hweq, hjeq, hj0_or_val]
                    have h2y : (wiresFrom D.gates (List.ofFn y)).getD w2 false = true :=
                      (hS2 y).2 (by simp [hyv])
                    rw [h2y, Bool.or_true]
                  · set acc_j := elimFPass n (D.gates.take (w - n)) (initFVar n u, [])
                    have hacc_j_len : acc_j.1.length = n + (w - n) := by
                      rw [elimFPass_fst_len, show (initFVar n u).length = n by simp [initFVar], List.length_take, Nat.min_eq_left hj.le]
                    have hst_w : acc.1.getD w none = (elimFStep n acc_j D.gates[w - n]).1.getD (n + (w - n)) none := by
                      have hsplit : D.gates = D.gates.take (w - n) ++ D.gates[w - n] :: D.gates.drop (w - n + 1) := by simp
                      conv_lhs => rw [← hweq, hacc, hsplit, elimFPass_append, elimFPass_cons]
                      have hstep_len : (elimFStep n acc_j D.gates[w - n]).1.length = n + (w - n) + 1 := by
                        unfold elimFStep
                        rcases (hDmono D.gates[w - n] (List.getElem_mem hj)).1 with hop | hop
                        · rw [hop]; dsimp only; split_ifs <;> simp [hacc_j_len]
                        · rw [hop]; dsimp only; split <;> simp [hacc_j_len]
                      exact elimFPass_getD_lt _ _ _ (by rw [hstep_len]; omega)
                    have hin_ne : ∀ i ∈ D.gates[w - n].inputs, acc_j.1.getD i none ≠ none := by
                      intro i hi hnone
                      rcases (hDmono D.gates[w - n] (List.getElem_mem hj)).1 with hop | hop
                      · have hany : (D.gates[w - n].inputs.map fun k => acc_j.1.getD k none).any Option.isNone = true :=
                          List.any_eq_true.2 ⟨none, List.mem_map.2 ⟨i, hi, hnone⟩, rfl⟩
                        have hwn : (elimFStep n acc_j D.gates[w - n]).1.getD (n + (w - n)) none = none := by
                          unfold elimFStep; rw [hop]; dsimp only; rw [if_pos hany, ← hacc_j_len, getD_snoc_eq]
                        exact hne (hst_w.trans hwn)
                      · exact hno_other (w - n) hj hjeq hop i hi hnone
                    have hin_lt : ∀ i ∈ D.gates[w - n].inputs, i < n + (w - n) := by
                      intro i hi
                      by_contra hge; push_neg at hge
                      exact hin_ne i hi (List.getD_eq_default _ _ (by omega))
                    have hgd1 := wiresFrom_gate_getD D.gates (List.ofFn x) hj
                    have hgd2 := wiresFrom_gate_getD D.gates (List.ofFn y) hj
                    simp only [List.length_ofFn, hweq] at hgd1 hgd2
                    rw [hgd1] at hval; rw [hgd2]
                    refine eval_mono_op (D.gates[w - n]).op (by simpa using (hDmono D.gates[w - n] (List.getElem_mem hj)).1) _ _ (by simp) ?_ hval
                    intro k hk h1
                    simp only [List.getElem_map] at h1 ⊢
                    have hk' : k < D.gates[w - n].inputs.length := by simpa using hk
                    set idx := D.gates[w - n].inputs[k]'hk'
                    have hidx_mem : idx ∈ D.gates[w - n].inputs := List.getElem_mem hk'
                    have hidx_lt : idx < n + (w - n) := hin_lt idx hidx_mem
                    change (wiresFrom (D.gates.take (w - n)) (List.ofFn x)).getD idx false = true at h1
                    change (wiresFrom (D.gates.take (w - n)) (List.ofFn y)).getD idx false = true
                    rw [wiresFrom_take_getD _ _ hj (by simp; exact hidx_lt)] at h1 ⊢
                    have hidx_ne : acc.1.getD idx none ≠ none := by
                      have hsplit : D.gates = D.gates.take (w - n) ++ D.gates.drop (w - n) := (List.take_append_drop _ _).symm
                      rw [hacc]; conv_lhs => rw [hsplit, elimFPass_append]
                      rw [elimFPass_getD_lt _ _ _ (by rw [hacc_j_len]; exact hidx_lt)]
                      exact hin_ne idx hidx_mem
                    exact ihw idx (by omega) (by omega) hidx_ne h1
            have hout_lt : D.output < n + D.gates.length := by
              by_contra hge; push_neg at hge
              have hlen : acc.1.length = n + D.gates.length := by
                rw [hacc, elimFPass_fst_len, show (initFVar n u).length = n by simp [initFVar]]
              rw [List.getD_eq_default _ _ (by omega)] at hout; cases hout
            by_cases huv_adj : G.Adj u v
            · -- u ~ v: pairVec u v ≤ unitVec v -> contradiction!
              have h1 : D.eval (List.ofFn (unitVec v)) = true := hcmp (pairVec u v) (unitVec v) (fun i hiu hi => by
                simp only [pairVec, decide_eq_true_eq] at hi
                rcases hi with rfl | rfl
                · exact absurd rfl hiu
                · simp [unitVec]) (by simp [unitVec]) D.output hout_lt (by rw [hout]; simp) (hDcomp.1 u v huv_adj)
              rw [hDcomp.2.1 v] at h1; cases h1
            · -- ¬ u ~ v: both r1, r2 are adjacent to v -> 4-cycle u - r1 - v - r2 - u!
              have hvr1 : G.Adj v r1 := by
                by_contra hnot
                have h1 : D.eval (List.ofFn (pairVec v r1)) = true := hcmp (pairVec u r1) (pairVec v r1) (fun i hiu hi => by
                  simp only [pairVec, decide_eq_true_eq] at hi ⊢
                  rcases hi with rfl | rfl
                  · exact absurd rfl hiu
                  · exact Or.inr rfl) (by simp [pairVec]) D.output hout_lt (by rw [hout]; simp) (hDcomp.1 u r1 hur1)
                rw [hDcomp.2.2 v r1 hnot] at h1; cases h1
              have hvr2 : G.Adj v r2 := by
                by_contra hnot
                have h1 : D.eval (List.ofFn (pairVec v r2)) = true := hcmp (pairVec u r2) (pairVec v r2) (fun i hiu hi => by
                  simp only [pairVec, decide_eq_true_eq] at hi ⊢
                  rcases hi with rfl | rfl
                  · exact absurd rfl hiu
                  · exact Or.inr rfl) (by simp [pairVec]) D.output hout_lt (by rw [hout]; simp) (hDcomp.1 u r2 hur2)
                rw [hDcomp.2.2 v r2 hnot] at h1; cases h1
              have hur1_ne : u ≠ r1 := fun e => G.irrefl (e ▸ hur1)
              have hur2_ne : u ≠ r2 := fun e => G.irrefl (e ▸ hur2)
              have hvr1_ne : v ≠ r1 := fun e => G.irrefl (e ▸ hvr1)
              have hvr2_ne : v ≠ r2 := fun e => G.irrefl (e ▸ hvr2)
              let cyc : G.Walk u u :=
                SimpleGraph.Walk.cons hur1
                  (SimpleGraph.Walk.cons hvr1.symm
                    (SimpleGraph.Walk.cons hvr2
                      (SimpleGraph.Walk.cons hur2.symm SimpleGraph.Walk.nil)))
              have hcyc_is : cyc.IsCycle := by
                rw [SimpleGraph.Walk.isCycle_def]
                refine ⟨?_, by simp [cyc], ?_⟩
                · rw [SimpleGraph.Walk.isTrail_def]
                  simp only [cyc, SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_nil, List.nodup_cons,
                    List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, not_false_eq_true, and_true]
                  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩ <;> intro h <;>
                    rcases Sym2.eq_iff.1 h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
                    first | exact huv_ne h1 | exact huv_ne h1.symm | exact huv_ne h2 | exact huv_ne h2.symm
                          | exact hr12 h1 | exact hr12 h1.symm | exact hr12 h2 | exact hr12 h2.symm
                          | exact hur1_ne h1 | exact hur1_ne h1.symm | exact hur1_ne h2 | exact hur1_ne h2.symm
                          | exact hur2_ne h1 | exact hur2_ne h1.symm | exact hur2_ne h2 | exact hur2_ne h2.symm
                          | exact hvr1_ne h1 | exact hvr1_ne h1.symm | exact hvr1_ne h2 | exact hvr1_ne h2.symm
                          | exact hvr2_ne h1 | exact hvr2_ne h1.symm | exact hvr2_ne h2 | exact hvr2_ne h2.symm
                · simp [cyc, hr12, hr12.symm, huv_ne, huv_ne.symm, hur1_ne, hur1_ne.symm,
                    hur2_ne, hur2_ne.symm, hvr1_ne, hvr1_ne.symm, hvr2_ne, hvr2_ne.symm]
              exact hnoC4 u cyc hcyc_is rfl
          have hor_drop := elimFPass_orCount_add_dropped n D.gates (initFVar n u) (fun g hg => (hDmono g hg).1)
          have hIH := ih G'.edgeSet.ncard (by omega) n G' ⟨acc.2, out⟩ rfl hG'sparse hG'noC4 hD'mono hD'comp
          change orCount ⟨acc.2, out⟩ + dropSet.card = orCount D at hor_drop
          omega

end PEqualNP.Outside.L_meta_599_aux

theorem PEqualNP.Outside.L_meta_599 :
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (A : Finset ℕ),
      (∀ S : Finset (Fin n), {e : Sym2 (Fin n) | e ∈ G.edgeSet ∧ ∀ v ∈ e, v ∈ S}.ncard ≤ S.card) →
      (∀ (v : Fin n) (c : G.Walk v v), c.IsCycle → c.length ≠ 4) →
      PEqualNP.MetaComplexity.Monotone2 C →
      (∀ x : Fin n → Bool, C.eval (List.ofFn x) = true ↔ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) →
      (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.or → j ∈ A) →
      G.edgeSet.ncard ≤ A.card + 1 := by
  intro n G C A hsparse hnoC4 hmono heval hA
  have h1 := PEqualNP.Outside.L_meta_599_aux.main_599 G.edgeSet.ncard n G C rfl hsparse hnoC4 hmono
    (PEqualNP.Outside.L_meta_599_aux.computesEdges_of_eval heval)
  have h2 := PEqualNP.Outside.L_meta_599_aux.orCount_le_card hA
  omega
