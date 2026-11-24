import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2415

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm

def fd {α : Type} (st : List α → Gate → α) (gs : List Gate) (w : List α) : List α :=
  gs.foldl (fun w g => w ++ [st w g]) w

theorem fd_snoc {α : Type} (st : List α → Gate → α) (gs : List Gate) (g : Gate) (w : List α) :
    fd st (gs ++ [g]) w = fd st gs w ++ [st (fd st gs w) g] := by
  simp [fd, List.foldl_append]

theorem fd_len {α : Type} (st : List α → Gate → α) (gs : List Gate) :
    ∀ w : List α, (fd st gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [fd]
  | cons g gs ih =>
    intro w
    have := ih (w ++ [st w g])
    simp only [fd, List.foldl_cons] at this ⊢
    rw [this]; simp; omega

theorem fd_keep {α : Type} (st : List α → Gate → α) (d : α) (gs : List Gate) :
    ∀ (w : List α) (i : ℕ), i < w.length → (fd st gs w).getD i d = w.getD i d := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    have := ih (w ++ [st w g]) i (by simp; omega)
    simp only [fd, List.foldl_cons] at this ⊢
    rw [this]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem fd_take {α : Type} (st : List α → Gate → α) (d : α) (gs : List Gate) (X : List α)
    (k i : ℕ) (hi : i < X.length + k) (hk : k ≤ gs.length) :
    (fd st gs X).getD i d = (fd st (gs.take k) X).getD i d := by
  have h1 : fd st gs X = fd st (gs.drop k) (fd st (gs.take k) X) := by
    unfold fd
    rw [← List.foldl_append, List.take_append_drop]
  rw [h1]
  exact fd_keep st d _ _ i (by rw [fd_len, List.length_take, Nat.min_eq_left hk]; exact hi)

theorem fd_gate {α : Type} (st : List α → Gate → α) (d : α) (gs : List Gate) (X : List α)
    (k : ℕ) (hk : k < gs.length) :
    (fd st gs X).getD (X.length + k) d = st (fd st (gs.take k) X) gs[k] := by
  rw [fd_take st d gs X (k + 1) _ (by omega) hk, List.take_succ_eq_append_getElem hk, fd_snoc]
  have hl : (fd st (gs.take k) X).length = X.length + k := by
    rw [fd_len, List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)]
  rw [← hl]
  simp [List.getD_eq_getElem?_getD]

def stB (w : List Bool) (g : Gate) : Bool := g.op.eval (g.inputs.map fun i => w.getD i false)

def val (gs : List Gate) {n : ℕ} (w : ℕ) (x : Fin n → Bool) : Bool :=
  (fd stB gs (List.ofFn x)).getD w false

theorem eval_eq (C : Circuit) {n : ℕ} (x : Fin n → Bool) :
    circuitFun n C x = val C.gates C.output x := rfl

theorem iv_eq (gs : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k ≤ gs.length)
    (i : ℕ) : (fd stB (gs.take k) (List.ofFn x)).getD i false = true ↔
      i < n + k ∧ val gs i x = true := by
  by_cases hi : i < n + k
  · rw [val, fd_take stB false gs (List.ofFn x) k i (by simpa using hi) hk]
    simp [hi]
  · rw [List.getD_eq_default _ _ (by rw [fd_len, List.length_take, Nat.min_eq_left hk]; simp; omega)]
    simp [hi]

theorem val_and (gs : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k < gs.length)
    (hop : gs[k].op = GateOp.and) :
    val gs (n + k) x = true ↔ ∀ i ∈ gs[k].inputs, i < n + k ∧ val gs i x = true := by
  have := fd_gate stB false gs (List.ofFn x) k hk
  rw [List.length_ofFn] at this
  rw [val, this]
  show (gs[k].op.eval _) = true ↔ _
  rw [hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
  constructor
  · intro h i hi; exact (iv_eq gs x k (Nat.le_of_lt hk) i).1 (h i hi)
  · intro h i hi; exact (iv_eq gs x k (Nat.le_of_lt hk) i).2 (h i hi)

theorem val_or (gs : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k < gs.length)
    (hop : gs[k].op = GateOp.or) :
    val gs (n + k) x = true ↔ ∃ i ∈ gs[k].inputs, i < n + k ∧ val gs i x = true := by
  have := fd_gate stB false gs (List.ofFn x) k hk
  rw [List.length_ofFn] at this
  rw [val, this]
  show (gs[k].op.eval _) = true ↔ _
  rw [hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
  constructor
  · rintro ⟨i, hi, h⟩; exact ⟨i, hi, (iv_eq gs x k (Nat.le_of_lt hk) i).1 h⟩
  · rintro ⟨i, hi, h⟩; exact ⟨i, hi, (iv_eq gs x k (Nat.le_of_lt hk) i).2 h⟩

theorem val_input (gs : List Gate) {n : ℕ} (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    val gs w x = x ⟨w, hw⟩ := by
  rw [val, fd_keep stB false gs _ w (by simpa using hw)]
  simp [List.getD_eq_getElem?_getD, hw]

theorem gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k = C.gates[k] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]

def Rr (n : ℕ) (C : Circuit) : ℕ → ℕ → Prop :=
  Relation.ReflTransGen (fun ra rb => ra < rb ∧ ∃ rj, rb = n + rj ∧ rj < C.gates.length ∧
    (gateAt C rj).op = GateOp.or ∧ ra ∈ (gateAt C rj).inputs)

theorem or_path (n : ℕ) (C : Circuit) (x : Fin n → Bool) (a b : ℕ) (h : Rr n C a b) :
    val C.gates a x = true → val C.gates b x = true := by
  unfold Rr at h
  induction h with
  | refl => exact id
  | tail _ hs ih =>
    intro ha
    obtain ⟨hlt, rj, rfl, hj, hop, hin⟩ := hs
    rw [gateAt_eq C rj hj] at hop hin
    exact (val_or C.gates x rj hj hop).2 ⟨_, hin, hlt, ih ha⟩


theorem snoc_rel {α : Type} (R : α → α → Prop) (z : α) (hz : R z z) {l l' : List α} {a b : α}
    (hl : l.length = l'.length) (h : ∀ i, R (l.getD i z) (l'.getD i z)) (hab : R a b) (i : ℕ) :
    R ((l ++ [a]).getD i z) ((l' ++ [b]).getD i z) := by
  by_cases hi : i < l'.length
  · rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ hi]
    exact h i
  · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega), hl]
    by_cases h0 : i - l'.length = 0
    · rw [h0]
      simp only [List.getD_cons_zero]
      exact hab
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
      exact hz

theorem all_mono (w w' : List Bool) (h : ∀ i, w.getD i false = true → w'.getD i false = true) (ins : List ℕ) :
    (ins.map fun i => w.getD i false).all id = true → (ins.map fun i => w'.getD i false).all id = true := by
  induction ins with
  | nil => intro _; rfl
  | cons a t ih =>
    simp only [List.map_cons, List.all_cons, Bool.and_eq_true, id_eq]
    exact fun hh => ⟨h a hh.1, ih hh.2⟩

theorem any_mono (w w' : List Bool) (h : ∀ i, w.getD i false = true → w'.getD i false = true) (ins : List ℕ) :
    (ins.map fun i => w.getD i false).any id = true → (ins.map fun i => w'.getD i false).any id = true := by
  induction ins with
  | nil => intro hh; exact hh
  | cons a t ih =>
    simp only [List.map_cons, List.any_cons, Bool.or_eq_true, id_eq]
    exact fun hh => hh.elim (fun h1 => Or.inl (h a h1)) (fun h2 => Or.inr (ih h2))

def evg (g : Gate) (w : List Bool) : Bool := g.op.eval (g.inputs.map fun i => w.getD i false)

def runW (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem evg_mono (w w' : List Bool) (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or)
    (h : ∀ i, w.getD i false = true → w'.getD i false = true) :
    evg g w = true → evg g w' = true := by
  rcases hg with hg | hg
  · unfold evg
    rw [hg]
    exact all_mono w w' h g.inputs
  · unfold evg
    rw [hg]
    exact any_mono w w' h g.inputs

theorem run_mono : ∀ (gs : List Gate) (w w' : List Bool),
    w.length = w'.length → (∀ i, w.getD i false = true → w'.getD i false = true) →
      (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) →
        ∀ i, (runW gs w).getD i false = true → (runW gs w').getD i false = true
  | [], _, _, _, h, _ => h
  | g :: gs, w, w', hl, h, hg => by
    have h1 := evg_mono w w' g (hg g (by simp)) h
    exact run_mono gs (w ++ [evg g w]) (w' ++ [evg g w'])
      (by simp [hl]) (snoc_rel (fun a b : Bool => a = true → b = true) false (fun hh => hh) hl h h1)
      (fun g' hg' => hg g' (List.mem_cons_of_mem _ hg'))

theorem wires_mono (C : Circuit) (hC : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    {n : ℕ} (x y : Fin n → Bool) (h : ∀ k, x k = true → y k = true) (i : ℕ) :
    (C.wires (List.ofFn x)).getD i false = true → (C.wires (List.ofFn y)).getD i false = true := by
  refine run_mono C.gates (List.ofFn x) (List.ofFn y) (by simp) ?_ hC i
  intro k
  by_cases hk : k < n
  · have e : ∀ z : Fin n → Bool, (List.ofFn z).getD k false = z ⟨k, hk⟩ := fun z => by
      simp [List.getD_eq_getElem?_getD, hk]
    rw [e x, e y]
    exact h _
  · rw [List.getD_eq_default _ _ (by simp; omega)]
    intro hh
    exact (Bool.false_ne_true hh).elim


theorem or_pathw (n : ℕ) (C : Circuit) (x : Fin n → Bool) (a b : ℕ) (h : Rr n C a b) :
    (C.wires (List.ofFn x)).getD a false = true → (C.wires (List.ofFn x)).getD b false = true :=
  or_path n C x a b h

theorem Rr_refl (n : ℕ) (C : Circuit) (a : ℕ) : Rr n C a a := Relation.ReflTransGen.refl

theorem Rr_trans {n : ℕ} {C : Circuit} {a b c : ℕ} (h1 : Rr n C a b) (h2 : Rr n C b c) :
    Rr n C a c := Relation.ReflTransGen.trans h1 h2

theorem Rr_step (n : ℕ) (C : Circuit) (j c : ℕ) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.or) (hlt : c < n + j) (hin : c ∈ (gateAt C j).inputs) :
    Rr n C c (n + j) :=
  Relation.ReflTransGen.single ⟨hlt, j, rfl, hj, hop, hin⟩

theorem r_and (n : ℕ) (C : Circuit) (a j : ℕ) (hop : (gateAt C j).op = GateOp.and)
    (h : Rr n C a (n + j)) : a = n + j := by
  unfold Rr at h
  rcases Relation.ReflTransGen.cases_tail h with h1 | ⟨c, _, hs⟩
  · exact h1.symm
  · obtain ⟨_, rj, hrj, _, hop2, _⟩ := hs
    have hjj : j = rj := by omega
    subst hjj
    rw [hop] at hop2
    cases hop2

def sl : Bool → ℕ
  | true => 0
  | false => 1

theorem slot (n : ℕ) (C : Circuit) (hC : IsAO2 n C) (j : ℕ) (hj : j < C.gates.length) (c : ℕ)
    (hin : c ∈ (gateAt C j).inputs) : ∃ b : Bool, (gateAt C j).inputs.getD (sl b) 0 = c := by
  have hl : (gateAt C j).inputs.length = 2 := by
    rw [gateAt_eq C j hj]
    exact hC.2.2 _ (List.getElem_mem hj)
  obtain ⟨u, v, huv⟩ := List.length_eq_two.mp hl
  rw [huv] at hin ⊢
  have hin2 : c = u ∨ c = v := by simpa using hin
  rcases hin2 with h | h
  · exact ⟨true, by subst h; simp [sl]⟩
  · exact ⟨false, by subst h; simp [sl]⟩

theorem walk (n : ℕ) (C : Circuit) (hC : IsAO2 n C) (Lt : ℕ → Prop) (x y : ℕ)
    (h : Rr n C x y) (hx : Lt x) :
    Lt y ∨ ∃ (j : ℕ) (b : Bool), j < C.gates.length ∧ (gateAt C j).op = GateOp.or ∧
      (gateAt C j).inputs.getD (sl b) 0 < n + j ∧
      (gateAt C j).inputs.getD (sl b) 0 ∈ (gateAt C j).inputs ∧
      Rr n C x ((gateAt C j).inputs.getD (sl b) 0) ∧ Rr n C (n + j) y ∧
      Lt ((gateAt C j).inputs.getD (sl b) 0) ∧ ¬ Lt (n + j) := by
  unfold Rr at h
  induction h with
  | refl => exact Or.inl hx
  | @tail u v hab hs ih =>
    rcases ih with ih | ⟨j, bb, h1, h2, h3, h4, h5, h6, h7, h8⟩
    · by_cases hc : Lt v
      · exact Or.inl hc
      · obtain ⟨hlt, rj, hv, hj, hop, hin⟩ := hs
        subst hv
        obtain ⟨bb, hbb⟩ := slot n C hC rj hj u hin
        refine Or.inr ⟨rj, bb, hj, hop, ?_, ?_, ?_, Rr_refl n C _, ?_, hc⟩
        · rw [hbb]; exact hlt
        · rw [hbb]; exact hin
        · rw [hbb]; exact hab
        · rw [hbb]; exact ih
    · exact Or.inr ⟨j, bb, h1, h2, h3, h4, h5,
        Rr_trans h6 (Relation.ReflTransGen.single hs), h7, h8⟩

theorem count_tok {α : Type} (T : Finset α) (X : Set ℕ) (hfin : X.Finite)
    (Q : α → ℕ → Bool → Prop)
    (hex : ∀ e ∈ T, ∃ (j : ℕ) (b : Bool), j ∈ X ∧ Q e j b)
    (hinj : ∀ e ∈ T, ∀ e2 ∈ T, ∀ (j : ℕ) (b : Bool), Q e j b → Q e2 j b → e = e2) :
    T.card ≤ 2 * X.ncard := by
  classical
  choose! f g hf using hex
  rw [Set.ncard_eq_toFinset_card X hfin]
  have hle : T.card ≤ (hfin.toFinset ×ˢ (Finset.univ : Finset Bool)).card := by
    apply Finset.card_le_card_of_injOn (fun e => (f e, g e))
    · intro e he
      exact Finset.mem_product.mpr ⟨hfin.mem_toFinset.mpr (hf e he).1, Finset.mem_univ _⟩
    · intro e he e2 he2 h
      have h1 : f e = f e2 := congrArg Prod.fst h
      have h2 : g e = g e2 := congrArg Prod.snd h
      have q2 := (hf e2 he2).2
      rw [← h1, ← h2] at q2
      exact hinj e he e2 he2 (f e) (g e) (hf e he).2 q2
  rw [Finset.card_product, Finset.card_univ, Fintype.card_bool] at hle
  omega

theorem geo (n N M : ℕ) (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop)
    (C : Circuit) (hC : IsAO2 n C) (hpw : ∀ p2 : Fin N, pw p2 < n)
    (hsound : ∀ (P : Finset (Fin N)) (Y : Finset (Fin M)), P.card ≤ 2 → Y.card ≤ 2 →
      (∀ p3 ∈ P, ∀ l3 ∈ Y, ¬ I p3 l3) →
      circuitFun n C (fun k3 : Fin n => decide (k3.val ∈ P.image pw ∪ Y.image lw)) = false)
    (p : Fin N) (l : Fin M) (m s : ℕ) (hr : Rr n C s m)
    (hacc : ∀ z3 : Fin n → Bool, (∃ h3 : pw p < n, z3 ⟨pw p, h3⟩ = true) →
      (C.wires (List.ofFn z3)).getD m false = true → circuitFun n C z3 = true)
    (hdirty : ∀ pz6 : Fin N, ¬ I pz6 l → ∃ (P6 : Finset (Fin N)) (Y6 : Finset (Fin M)),
      P6.card ≤ 1 ∧ Y6.card ≤ 2 ∧ (∀ a6 ∈ insert pz6 P6, ∀ m6 ∈ Y6, ¬ I a6 m6) ∧
      (C.wires (List.ofFn (fun k6 : Fin n =>
        decide (k6.val ∈ P6.image pw ∪ Y6.image lw)))).getD s false = true) : I p l := by
  by_contra hn
  obtain ⟨P6, Y6, hc1, hc2, hno, hv⟩ := hdirty p hn
  have hz := hsound (insert p P6) Y6 ((Finset.card_insert_le _ _).trans (by omega)) hc2 hno
  have hm := wires_mono C hC.1
    (fun k6 : Fin n => decide (k6.val ∈ P6.image pw ∪ Y6.image lw))
    (fun k3 : Fin n => decide (k3.val ∈ (insert p P6).image pw ∪ Y6.image lw))
    (by
      intro k hk
      rw [decide_eq_true_eq] at hk ⊢
      rcases Finset.mem_union.mp hk with h | h
      · exact Finset.mem_union_left _
          (Finset.image_subset_image (Finset.subset_insert _ _) h)
      · exact Finset.mem_union_right _ h) s hv
  have hm2 := or_pathw n C
    (fun k3 : Fin n => decide (k3.val ∈ (insert p P6).image pw ∪ Y6.image lw)) s m hr hm
  have h := hacc _ ⟨hpw p, decide_eq_true (Finset.mem_union_left _
    (Finset.mem_image_of_mem pw (Finset.mem_insert_self p P6)))⟩ hm2
  rw [hz] at h
  exact Bool.false_ne_true h

theorem core (n : ℕ) (C : Circuit) (hC : IsAO2 n C) {N M : ℕ} (A : Finset (Fin N × Fin M))
    (Rd G m S Sy : Fin N × Fin M → ℕ)
    (hRd : ∀ e ∈ A, Rd e < C.gates.length ∧ (gateAt C (Rd e)).op = GateOp.and ∧
      (((gateAt C (Rd e)).inputs.getD 0 0 = G e ∧ (gateAt C (Rd e)).inputs.getD 1 0 = m e) ∨
       ((gateAt C (Rd e)).inputs.getD 0 0 = m e ∧ (gateAt C (Rd e)).inputs.getD 1 0 = G e)))
    (hG : ∀ e ∈ A, ∀ e2 ∈ A, G e = G e2 → e.1 = e2.1)
    (hS : ∀ e ∈ A, S e < C.gates.length ∧ (gateAt C (S e)).op = GateOp.and ∧
      ((gateAt C (S e)).inputs.getD 0 0 = Sy e ∨ (gateAt C (S e)).inputs.getD 1 0 = Sy e))
    (hSy : ∀ e ∈ A, ∀ e2 ∈ A, Sy e = Sy e2 → e.2 = e2.2)
    (hpath : ∀ e ∈ A, Rr n C (n + S e) (m e))
    (huniq : ∀ e1 ∈ A, ∀ e2 ∈ A, ∀ e ∈ A, ∀ e3 ∈ A, ∀ w : ℕ, Rr n C (n + S e1) w →
      Rr n C (n + S e2) w → e1.2 ≠ e2.2 → Rr n C w (m e) → Rr n C w (m e3) → e.1 = e3.1) :
    A.card ≤ 2 * (2 * {ja : ℕ | ja < C.gates.length ∧ (gateAt C ja).op = GateOp.and}.ncard +
      {jo : ℕ | jo < C.gates.length ∧ (gateAt C jo).op = GateOp.or}.ncard) := by
  classical
  have hfa : {ja : ℕ | ja < C.gates.length ∧ (gateAt C ja).op = GateOp.and}.Finite :=
    (Set.finite_lt_nat C.gates.length).subset (fun j hj => hj.1)
  have hfo : {jo : ℕ | jo < C.gates.length ∧ (gateAt C jo).op = GateOp.or}.Finite :=
    (Set.finite_lt_nat C.gates.length).subset (fun j hj => hj.1)
  have hsub : A ⊆ A.filter (fun e => ∃ e2 ∈ A, S e2 = S e ∧ e2.2 ≠ e.2) ∪
      (A.filter (fun e => ∀ e2 ∈ A, Rr n C (n + S e2) (m e) → e2.2 = e.2) ∪
       A.filter (fun e => (¬ ∃ e2 ∈ A, S e2 = S e ∧ e2.2 ≠ e.2) ∧
         ¬ ∀ e2 ∈ A, Rr n C (n + S e2) (m e) → e2.2 = e.2)) := by
    intro e he
    simp only [Finset.mem_union, Finset.mem_filter]
    by_cases h1 : ∃ e2 ∈ A, S e2 = S e ∧ e2.2 ≠ e.2
    · exact Or.inl ⟨he, h1⟩
    · by_cases h2 : ∀ e2 ∈ A, Rr n C (n + S e2) (m e) → e2.2 = e.2
      · exact Or.inr (Or.inl ⟨he, h2⟩)
      · exact Or.inr (Or.inr ⟨he, h1, h2⟩)
  have c1 : (A.filter (fun e => ∃ e2 ∈ A, S e2 = S e ∧ e2.2 ≠ e.2)).card ≤
      2 * {ja : ℕ | ja < C.gates.length ∧ (gateAt C ja).op = GateOp.and}.ncard := by
    refine count_tok _ _ hfa
      (fun e j b => S e = j ∧ (gateAt C j).inputs.getD (sl b) 0 = Sy e) ?_ ?_
    · intro e he
      have heA := (Finset.mem_filter.mp he).1
      obtain ⟨hlt, hop, h0 | h1⟩ := hS e heA
      · exact ⟨S e, true, ⟨hlt, hop⟩, rfl, h0⟩
      · exact ⟨S e, false, ⟨hlt, hop⟩, rfl, h1⟩
    · intro e he e3 he3 j b hq hq3
      obtain ⟨heA, e2, he2, hs2, hne⟩ := Finset.mem_filter.mp he
      have he3A := (Finset.mem_filter.mp he3).1
      obtain ⟨hj, hs⟩ := hq
      obtain ⟨hj3, hs3⟩ := hq3
      have hl : e.2 = e3.2 := hSy e heA e3 he3A (hs.symm.trans hs3)
      have hSS : S e3 = S e := hj3.trans hj.symm
      have hp : e.1 = e3.1 := by
        refine huniq e2 he2 e heA e heA e3 he3A (n + S e) ?_ (Rr_refl n C _) hne
          (hpath e heA) ?_
        · rw [hs2]; exact Rr_refl n C _
        · rw [← hSS]; exact hpath e3 he3A
      exact Prod.ext hp hl
  have c2 : (A.filter (fun e => ∀ e2 ∈ A, Rr n C (n + S e2) (m e) → e2.2 = e.2)).card ≤
      2 * {ja : ℕ | ja < C.gates.length ∧ (gateAt C ja).op = GateOp.and}.ncard := by
    refine count_tok _ _ hfa
      (fun e j b => Rd e = j ∧ (gateAt C j).inputs.getD (sl b) 0 = G e ∧
        (gateAt C j).inputs.getD (sl (!b)) 0 = m e) ?_ ?_
    · intro e he
      have heA := (Finset.mem_filter.mp he).1
      obtain ⟨hlt, hop, h0 | h1⟩ := hRd e heA
      · exact ⟨Rd e, true, ⟨hlt, hop⟩, rfl, h0.1, h0.2⟩
      · exact ⟨Rd e, false, ⟨hlt, hop⟩, rfl, h1.2, h1.1⟩
    · intro e he e3 he3 j b hq hq3
      obtain ⟨heA, hL⟩ := Finset.mem_filter.mp he
      have he3A := (Finset.mem_filter.mp he3).1
      obtain ⟨_, hg, hm⟩ := hq
      obtain ⟨_, hg3, hm3⟩ := hq3
      have hp : e.1 = e3.1 := hG e heA e3 he3A (hg.symm.trans hg3)
      have hmm : m e3 = m e := hm3.symm.trans hm
      have hl : e3.2 = e.2 := hL e3 he3A (by rw [← hmm]; exact hpath e3 he3A)
      exact Prod.ext hp hl.symm
  have c3 : (A.filter (fun e => (¬ ∃ e2 ∈ A, S e2 = S e ∧ e2.2 ≠ e.2) ∧
         ¬ ∀ e2 ∈ A, Rr n C (n + S e2) (m e) → e2.2 = e.2)).card ≤
      2 * {jo : ℕ | jo < C.gates.length ∧ (gateAt C jo).op = GateOp.or}.ncard := by
    refine count_tok _ _ hfo
      (fun e j b => j < C.gates.length ∧ (gateAt C j).op = GateOp.or ∧
        (gateAt C j).inputs.getD (sl b) 0 < n + j ∧
        (gateAt C j).inputs.getD (sl b) 0 ∈ (gateAt C j).inputs ∧
        Rr n C (n + S e) ((gateAt C j).inputs.getD (sl b) 0) ∧ Rr n C (n + j) (m e) ∧
        (∀ e2 ∈ A, Rr n C (n + S e2) ((gateAt C j).inputs.getD (sl b) 0) → e2.2 = e.2) ∧
        ¬ ∀ e2 ∈ A, Rr n C (n + S e2) (n + j) → e2.2 = e.2) ?_ ?_
    · intro e he
      obtain ⟨heA, h1, h2⟩ := Finset.mem_filter.mp he
      have hbase : ∀ e2 ∈ A, Rr n C (n + S e2) (n + S e) → e2.2 = e.2 := by
        intro e2 he2 hr
        by_contra hne
        have := r_and n C _ _ (hS e heA).2.1 hr
        exact h1 ⟨e2, he2, by omega, hne⟩
      rcases walk n C hC (fun x => ∀ e2 ∈ A, Rr n C (n + S e2) x → e2.2 = e.2)
        (n + S e) (m e) (hpath e heA) hbase with hw | ⟨j, b, w1, w2, w3, w4, w5, w6, w7, w8⟩
      · exact absurd hw h2
      · exact ⟨j, b, ⟨w1, w2⟩, w1, w2, w3, w4, w5, w6, w7, w8⟩
    · intro e he e3 he3 j b hq hq3
      have heA := (Finset.mem_filter.mp he).1
      have he3A := (Finset.mem_filter.mp he3).1
      obtain ⟨q1, q2, q3, q4, q5, q6, q7, q8⟩ := hq
      obtain ⟨_, _, _, _, r5, r6, _, _⟩ := hq3
      have hstep := Rr_step n C j _ q1 q2 q3 q4
      have hl : e3.2 = e.2 := q7 e3 he3A r5
      have q9 : ∃ e2 ∈ A, Rr n C (n + S e2) (n + j) ∧ e2.2 ≠ e.2 := by
        by_contra hcon
        apply q8
        intro e2 he2 hr
        by_contra hne
        exact hcon ⟨e2, he2, hr, hne⟩
      obtain ⟨e2, he2, hr2, hne⟩ := q9
      have hp : e.1 = e3.1 :=
        huniq e2 he2 e heA e heA e3 he3A (n + j) hr2 (Rr_trans q5 hstep) hne q6 r6
      exact Prod.ext hp hl.symm
  have u0 := Finset.card_le_card hsub
  have u1 := Finset.card_union_le (A.filter (fun e => ∃ e2 ∈ A, S e2 = S e ∧ e2.2 ≠ e.2))
    (A.filter (fun e => ∀ e2 ∈ A, Rr n C (n + S e2) (m e) → e2.2 = e.2) ∪
       A.filter (fun e => (¬ ∃ e2 ∈ A, S e2 = S e ∧ e2.2 ≠ e.2) ∧
         ¬ ∀ e2 ∈ A, Rr n C (n + S e2) (m e) → e2.2 = e.2))
  have u2 := Finset.card_union_le
    (A.filter (fun e => ∀ e2 ∈ A, Rr n C (n + S e2) (m e) → e2.2 = e.2))
    (A.filter (fun e => (¬ ∃ e2 ∈ A, S e2 = S e ∧ e2.2 ≠ e.2) ∧
         ¬ ∀ e2 ∈ A, Rr n C (n + S e2) (m e) → e2.2 = e.2))
  omega

theorem main (n N M : ℕ) (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop)
    (C : Circuit) (A : Finset (Fin N × Fin M)) (Rd G m S Sy : Fin N × Fin M → ℕ)
    (hC : IsAO2 n C) (hpw : ∀ p2 : Fin N, pw p2 < n)
    (hK : ∀ (p4 p5 : Fin N) (l4 l5 : Fin M), p4 ≠ p5 → l4 ≠ l5 →
      ¬ (I p4 l4 ∧ I p5 l4 ∧ I p4 l5 ∧ I p5 l5))
    (hsound : ∀ (P : Finset (Fin N)) (Y : Finset (Fin M)), P.card ≤ 2 → Y.card ≤ 2 →
      (∀ p3 ∈ P, ∀ l3 ∈ Y, ¬ I p3 l3) →
      circuitFun n C (fun k3 : Fin n => decide (k3.val ∈ P.image pw ∪ Y.image lw)) = false)
    (hA : ∀ e ∈ A, I e.1 e.2 ∧ ((Rd e) < C.gates.length ∧ (gateAt C (Rd e)).op = GateOp.and ∧
      ((((gateAt C (Rd e)).inputs.getD 0 0) = (G e) ∧ ((gateAt C (Rd e)).inputs.getD 1 0) = (m e)) ∨
       (((gateAt C (Rd e)).inputs.getD 0 0) = (m e) ∧ ((gateAt C (Rd e)).inputs.getD 1 0) = (G e)))) ∧
      {x1 : Fin N | Rr n C (pw x1) (G e)} = {e.1} ∧
      (∃ o : ℕ, ((S e) < C.gates.length ∧ (gateAt C (S e)).op = GateOp.and ∧
        ((((gateAt C (S e)).inputs.getD 0 0) = (Sy e) ∧ ((gateAt C (S e)).inputs.getD 1 0) = o) ∨
         (((gateAt C (S e)).inputs.getD 0 0) = o ∧ ((gateAt C (S e)).inputs.getD 1 0) = (Sy e))))) ∧
      {y2 : Fin M | Rr n C (lw y2) (Sy e)} = {e.2} ∧ Rr n C (n + S e) (m e) ∧
      (∀ z3 : Fin n → Bool, (∃ h3 : pw e.1 < n, z3 ⟨pw e.1, h3⟩ = true) →
        (C.wires (List.ofFn z3)).getD ((m e)) false = true → circuitFun n C z3 = true) ∧
      (∀ pz6 : Fin N, ¬ I pz6 e.2 → ∃ (P6 : Finset (Fin N)) (Y6 : Finset (Fin M)),
        P6.card ≤ 1 ∧ Y6.card ≤ 2 ∧ (∀ a6 ∈ insert pz6 P6, ∀ m6 ∈ Y6, ¬ I a6 m6) ∧
        (C.wires (List.ofFn (fun k6 : Fin n =>
          decide (k6.val ∈ P6.image pw ∪ Y6.image lw)))).getD ((n + S e)) false = true)) :
    A.card ≤ 2 * (2 * {ja : ℕ | ja < C.gates.length ∧ (gateAt C ja).op = GateOp.and}.ncard +
      {jo : ℕ | jo < C.gates.length ∧ (gateAt C jo).op = GateOp.or}.ncard) := by
  have key : ∀ e ∈ A, ∀ e2 ∈ A, Rr n C (n + S e2) (m e) → I e.1 e2.2 := by
    intro e he e2 he2 hr
    obtain ⟨_, _, _, _, _, _, hacc, _⟩ := hA e he
    obtain ⟨_, _, _, _, _, _, _, hdirty⟩ := hA e2 he2
    exact geo n N M pw lw I C hC hpw hsound e.1 e2.2 (m e) (n + S e2) hr hacc hdirty
  refine core n C hC A Rd G m S Sy (fun e he => (hA e he).2.1) ?_ ?_ ?_
    (fun e he => (hA e he).2.2.2.2.2.1) ?_
  · intro e he e2 he2 h
    have h1 := (hA e he).2.2.1
    have h2 := (hA e2 he2).2.2.1
    rw [h] at h1
    exact Set.singleton_injective (h1.symm.trans h2)
  · intro e he
    obtain ⟨o, hlt, hop, h⟩ := (hA e he).2.2.2.1
    exact ⟨hlt, hop, h.elim (fun x => Or.inl x.1) (fun x => Or.inr x.2)⟩
  · intro e he e2 he2 h
    have h1 := (hA e he).2.2.2.2.1
    have h2 := (hA e2 he2).2.2.2.2.1
    rw [h] at h1
    exact Set.singleton_injective (h1.symm.trans h2)
  · intro e1 he1 e2 he2 e he e3 he3 w h1 h2 hne hw hw3
    have a1 := key e he e1 he1 (Rr_trans h1 hw)
    have a2 := key e he e2 he2 (Rr_trans h2 hw)
    have a3 := key e3 he3 e1 he1 (Rr_trans h1 hw3)
    have a4 := key e3 he3 e2 he2 (Rr_trans h2 hw3)
    by_contra hp
    exact hK e.1 e3.1 e1.2 e2.2 hp hne ⟨a1, a3, a2, a4⟩

end PEqualNP.Outside.L_meta_2415

theorem PEqualNP.Outside.L_meta_2415 : ∀ (n N M : ℕ) (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop) (C : PEqualNP.CircuitLowerBounds.Circuit) (A : Finset (Fin N × Fin M)) (Rd G m S Sy : Fin N × Fin M → ℕ), PEqualNP.TopForm.IsAO2 n C → Function.Injective pw → Function.Injective lw → (∀ (p1 : Fin N) (l1 : Fin M), pw p1 ≠ lw l1) → (∀ p2 : Fin N, pw p2 < n) → (∀ l2 : Fin M, lw l2 < n) → (∀ (p4 p5 : Fin N) (l4 l5 : Fin M), p4 ≠ p5 → l4 ≠ l5 → ¬ (I p4 l4 ∧ I p5 l4 ∧ I p4 l5 ∧ I p5 l5)) → (∀ (P : Finset (Fin N)) (Y : Finset (Fin M)), P.card ≤ 2 → Y.card ≤ 2 → (∀ p3 ∈ P, ∀ l3 ∈ Y, ¬ I p3 l3) → PEqualNP.MetaComplexity.circuitFun n C (fun k3 : Fin n => decide (k3.val ∈ P.image pw ∪ Y.image lw)) = false) → ∀ R : ℕ → ℕ → Prop, R = Relation.ReflTransGen (fun ra rb => ra < rb ∧ ∃ rj, rb = n + rj ∧ rj < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ra ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).inputs) → (∀ e ∈ A, I e.1 e.2 ∧ ((Rd e) < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C (Rd e)).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((((PEqualNP.MetaComplexity.NestedCover.gateAt C (Rd e)).inputs.getD 0 0) = (G e) ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C (Rd e)).inputs.getD 1 0) = (m e)) ∨ (((PEqualNP.MetaComplexity.NestedCover.gateAt C (Rd e)).inputs.getD 0 0) = (m e) ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C (Rd e)).inputs.getD 1 0) = (G e)))) ∧ {x1 : Fin N | R (pw x1) (G e)} = {e.1} ∧ (∃ o : ℕ, ((S e) < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C (S e)).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((((PEqualNP.MetaComplexity.NestedCover.gateAt C (S e)).inputs.getD 0 0) = (Sy e) ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C (S e)).inputs.getD 1 0) = o) ∨ (((PEqualNP.MetaComplexity.NestedCover.gateAt C (S e)).inputs.getD 0 0) = o ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C (S e)).inputs.getD 1 0) = (Sy e))))) ∧ {y2 : Fin M | R (lw y2) (Sy e)} = {e.2} ∧ R (n + S e) (m e) ∧ (∀ z3 : Fin n → Bool, (∃ h3 : pw e.1 < n, z3 ⟨pw e.1, h3⟩ = true) → (C.wires (List.ofFn z3)).getD ((m e)) false = true → PEqualNP.MetaComplexity.circuitFun n C z3 = true) ∧ (∀ pz6 : Fin N, ¬ I pz6 e.2 → ∃ (P6 : Finset (Fin N)) (Y6 : Finset (Fin M)), P6.card ≤ 1 ∧ Y6.card ≤ 2 ∧ (∀ a6 ∈ insert pz6 P6, ∀ m6 ∈ Y6, ¬ I a6 m6) ∧ (C.wires (List.ofFn (fun k6 : Fin n => decide (k6.val ∈ P6.image pw ∪ Y6.image lw)))).getD ((n + S e)) false = true)) → A.card ≤ 2 * (2 * {ja : ℕ | ja < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C ja).op = PEqualNP.CircuitLowerBounds.GateOp.and}.ncard + {jo : ℕ | jo < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C jo).op = PEqualNP.CircuitLowerBounds.GateOp.or}.ncard) := by
  intro n N M pw lw I C A Rd G m S Sy hC _ _ _ hpw _ hK hsound R hR hA
  subst hR
  exact PEqualNP.Outside.L_meta_2415.main n N M pw lw I C A Rd G m S Sy hC hpw hK hsound hA
