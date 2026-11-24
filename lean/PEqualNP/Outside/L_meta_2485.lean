import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2485

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.CleanedNonEdge

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

theorem wires_eq (n : ℕ) (C : Circuit) (w : ℕ) (x : Fin n → Bool) :
    wireVal n C w x = val C.gates w x := rfl

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

theorem gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k = C.gates[k] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]

theorem orSets_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [orStep]
    omega

theorem orSets_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (orStep n) []).getD j [] ↔
      j < gs.length ∧ (i = j ∨ ((gs.getD j ⟨GateOp.or, []⟩).op = GateOp.or ∧
        ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
          i ∈ (gs.foldl (orStep n) []).getD (w - n) [])) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (orStep n) []).length = gs.length := by
      rw [orSets_len]; simp
    have key : ∀ k, k < gs.length →
        (orStep n (gs.foldl (orStep n) []) g).getD k [] =
          (gs.foldl (orStep n) []).getD k [] := by
      intro k hk
      simp only [orStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, h3⟩
        refine ⟨by simp; omega, ?_⟩
        rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
        · exact Or.inl h3
        · refine Or.inr ⟨hop, w, hw, h1, h2, ?_⟩
          rw [key (w - n) (by omega)]
          exact h3
      · rintro ⟨_, h3⟩
        refine ⟨h, ?_⟩
        rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
        · exact Or.inl h3
        · rw [key (w - n) (by omega)] at h3
          exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      rw [e1]
      by_cases hop : g.op = GateOp.or
      · have e2 : (orStep n (gs.foldl (orStep n) []) g).getD gs.length [] =
            gs.length :: (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
              (fun w => (gs.foldl (orStep n) []).getD (w - n) []) := by
          simp only [orStep, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp [hlen, hop]
        rw [e2]
        simp only [List.mem_cons, List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
        constructor
        · rintro (h3 | ⟨w, ⟨hw, h1, h2⟩, h3⟩)
          · exact ⟨by simp, Or.inl h3⟩
          · refine ⟨by simp, Or.inr ⟨hop, w, hw, h1, h2, ?_⟩⟩
            rw [key (w - n) (by omega)]
            exact h3
        · rintro ⟨_, h3 | ⟨_, w, hw, h1, h2, h3⟩⟩
          · exact Or.inl h3
          · rw [key (w - n) (by omega)] at h3
            exact Or.inr ⟨w, ⟨hw, h1, h2⟩, h3⟩
      · have e2 : (orStep n (gs.foldl (orStep n) []) g).getD gs.length [] = [gs.length] := by
          simp only [orStep, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp [hlen, hop]
        rw [e2]
        simp only [List.mem_singleton]
        constructor
        · intro h3
          exact ⟨by simp, Or.inl h3⟩
        · rintro ⟨_, h3 | ⟨hop2, _⟩⟩
          · exact h3
          · exact (hop hop2).elim
    · have e0 : (orStep n (gs.foldl (orStep n) []) g).getD j [] = [] := by
        simp only [orStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

theorem orReaches_iff (n : ℕ) (C : Circuit) (k g : ℕ) :
    OrReaches n C (n + k) g ↔ k < C.gates.length ∧ (g = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ i ∈ (gateAt C k).inputs, i < n + k ∧ OrReaches n C i g)) := by
  have h := orSets_char n C.gates g k
  unfold OrReaches orSets gateAt
  have e : n + k - n = k := by omega
  rw [e, h]
  constructor
  · rintro ⟨_, hk, h3⟩
    refine ⟨hk, ?_⟩
    rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
    · exact Or.inl h3
    · exact Or.inr ⟨hop, w, hw, h2, h1, h3⟩
  · rintro ⟨hk, h3⟩
    refine ⟨by omega, hk, ?_⟩
    rcases h3 with h3 | ⟨hop, w, hw, h2, h1, h3⟩
    · exact Or.inl h3
    · exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩

theorem reach_up (n : ℕ) (C : Circuit) (x : Fin n → Bool) (j : ℕ) :
    ∀ b : ℕ, OrReaches n C b j → val C.gates (n + j) x = true → val C.gates b x = true := by
  intro b
  induction b using Nat.strong_induction_on with
  | _ b ih =>
    intro h hv
    have hnb : n ≤ b := h.1
    obtain ⟨k, hbk⟩ : ∃ k, b = n + k := ⟨b - n, by omega⟩
    rw [hbk] at h ⊢
    obtain ⟨hk, h3⟩ := (orReaches_iff n C k j).1 h
    rcases h3 with h3 | ⟨hop, i, hi, hlt, hr⟩
    · rw [h3] at hv
      exact hv
    · rw [gateAt_eq C k hk] at hop hi
      exact (val_or C.gates x k hk hop).2 ⟨i, hi, hlt, ih i (by omega) hr hv⟩

theorem mem_filter' {α : Type} (p : α → Prop) (inst : DecidablePred p) (s : Finset α) (a : α) :
    a ∈ @Finset.filter α p inst s ↔ a ∈ s ∧ p a := Finset.mem_filter

theorem orIn_up (n : ℕ) (C : Circuit) (x : Fin n → Bool) (b : ℕ) (i : Fin n)
    (hi : i ∈ orIn n C b) (hv : val C.gates i.val x = true) : val C.gates b x = true := by
  have hi2 : (i : ℕ) = b ∨ ∃ k < C.gates.length,
      OrReaches n C b k ∧ (gateAt C k).op = GateOp.or ∧ (i : ℕ) ∈ (gateAt C k).inputs :=
    ((mem_filter' _ _ _ _).mp hi).2
  rcases hi2 with h1 | ⟨k, hk, hr, hop, hin⟩
  · rw [h1] at hv
    exact hv
  · rw [gateAt_eq C k hk] at hop hin
    have hlt : i.val < n + k := by
      have := i.isLt
      omega
    exact reach_up n C x k b hr ((val_or C.gates x k hk hop).2 ⟨i.val, hin, hlt, hv⟩)

theorem or_up (n : ℕ) (C : Circuit) (x : Fin n → Bool) (a b : ℕ)
    (h : (∃ i_1 : Fin n, i_1.val = a ∧ i_1 ∈ orIn n C b) ∨
      (∃ j_1 : ℕ, a = n + j_1 ∧ OrReaches n C b j_1))
    (hv : val C.gates a x = true) : val C.gates b x = true := by
  rcases h with ⟨i, hia, hi⟩ | ⟨j, haj, hr⟩
  · rw [← hia] at hv
    exact orIn_up n C x b i hi hv
  · rw [haj] at hv
    exact reach_up n C x j b hr hv

theorem and_eq (n : ℕ) (C : Circuit) (hC : IsAO2 n C) (x : Fin n → Bool) (j : ℕ)
    (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.and) :
    val C.gates (n + j) x = (val C.gates ((gateAt C j).inputs.getD 0 0) x &&
      val C.gates ((gateAt C j).inputs.getD 1 0) x) := by
  obtain ⟨_, hrb, hlen⟩ := hC
  have hrbj := hrb j hj
  rw [gateAt_eq C j hj] at hop hrbj ⊢
  have hl := hlen C.gates[j] (List.getElem_mem hj)
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hl
  have hva := val_and C.gates x j hj hop
  rw [hab] at hrbj hva ⊢
  simp only [List.getD_cons_zero, List.getD_cons_succ]
  rw [Bool.eq_iff_iff, Bool.and_eq_true, hva]
  constructor
  · intro h
    exact ⟨(h a (by simp)).2, (h b (by simp)).2⟩
  · rintro ⟨h0, h1⟩ i hi
    have hi2 : i = a ∨ i = b := by simpa using hi
    rcases hi2 with h2 | h2
    · rw [h2]
      exact ⟨hrbj a (by simp), h0⟩
    · rw [h2]
      exact ⟨hrbj b (by simp), h1⟩

theorem val_input (gs : List Gate) {n : ℕ} (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    val gs w x = x ⟨w, hw⟩ := by
  rw [val, fd_keep stB false gs _ w (by simpa using hw)]
  simp [List.getD_eq_getElem?_getD, hw]

def xs (n : ℕ) {K : ℕ} (f : Fin K → ℕ) (a : Fin K) : Fin n → Bool :=
  fun k => decide (k.val = f a)

def sh (n : ℕ) (C : Circuit) {K : ℕ} (f : Fin K → ℕ) (w : ℕ) : Set (Fin K) :=
  {a | wireVal n C w (fun k : Fin n => decide (k.val = f a)) = true}

def xin (n : ℕ) {N M : ℕ} (pw : Fin N → ℕ) (lw : Fin M → ℕ) (P : Finset (Fin N))
    (Y : Finset (Fin M)) : Fin n → Bool :=
  fun k => decide (k.val ∈ P.image pw ∪ Y.image lw)

def IsAnd (C : Circuit) (j a b : ℕ) : Prop :=
  j < C.gates.length ∧ (gateAt C j).op = GateOp.and ∧
    ((gateAt C j).inputs = [a, b] ∨ (gateAt C j).inputs = [b, a])

def Rch (n : ℕ) (C : Circuit) (a F : ℕ) : Prop :=
  (∃ i : Fin n, i.val = a ∧ i ∈ orIn n C F) ∨ (∃ j : ℕ, a = n + j ∧ OrReaches n C F j)

def Concl (n : ℕ) {N M : ℕ} (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop)
    (C : Circuit) (p : Fin N) (l : Fin M) : Prop :=
  (∃ a F, Rch n C a F ∧ sh n C lw a = {l} ∧ sh n C lw F ⊆ {m | I p m} ∧
      2 ≤ (sh n C lw F).ncard) ∨
  (∃ a F, Rch n C a F ∧ sh n C pw a = {p} ∧ sh n C pw F ⊆ {m | I m l} ∧
      2 ≤ (sh n C pw F).ncard) ∨
  (∃ j a b, IsAnd C j a b ∧ sh n C pw a = {p} ∧ sh n C lw b = {l}) ∨
  (∃ j K F V j2 F2 m, IsAnd C j K F ∧ sh n C pw K = {p} ∧ m ∈ sh n C lw F ∧ ¬ I p m ∧
      OrReaches n C V j ∧ IsAnd C j2 V F2 ∧ sh n C lw F2 = {l} ∧ OrReaches n C C.output j2)

theorem mem_sh (n : ℕ) (C : Circuit) {K : ℕ} (f : Fin K → ℕ) (w : ℕ) (a : Fin K) :
    a ∈ sh n C f w ↔ val C.gates w (xs n f a) = true := Iff.rfl

theorem and_iff (n : ℕ) (C : Circuit) (hC : IsAO2 n C) (x : Fin n → Bool) (j a b : ℕ)
    (h : IsAnd C j a b) :
    val C.gates (n + j) x = true ↔ val C.gates a x = true ∧ val C.gates b x = true := by
  obtain ⟨hj, hop, hin⟩ := h
  rw [and_eq n C hC x j hj hop, Bool.and_eq_true]
  rcases hin with h | h
  · rw [h]
    simp only [List.getD_cons_zero, List.getD_cons_succ]
  · rw [h]
    simp only [List.getD_cons_zero, List.getD_cons_succ]
    exact and_comm

theorem up_p (n : ℕ) (C : Circuit) (hC : IsAO2 n C) {N M : ℕ} (pw : Fin N → ℕ) (lw : Fin M → ℕ)
    (P : Finset (Fin N)) (Y : Finset (Fin M)) (a : Fin N) (ha : a ∈ P) (w : ℕ)
    (h : val C.gates w (xs n pw a) = true) : val C.gates w (xin n pw lw P Y) = true := by
  refine wires_mono C hC.1 _ _ ?_ w h
  intro k hk
  have e : k.val = pw a := of_decide_eq_true hk
  show decide (k.val ∈ P.image pw ∪ Y.image lw) = true
  rw [decide_eq_true_eq, e]
  exact Finset.mem_union_left _ (Finset.mem_image_of_mem pw ha)

theorem up_l (n : ℕ) (C : Circuit) (hC : IsAO2 n C) {N M : ℕ} (pw : Fin N → ℕ) (lw : Fin M → ℕ)
    (P : Finset (Fin N)) (Y : Finset (Fin M)) (a : Fin M) (ha : a ∈ Y) (w : ℕ)
    (h : val C.gates w (xs n lw a) = true) : val C.gates w (xin n pw lw P Y) = true := by
  refine wires_mono C hC.1 _ _ ?_ w h
  intro k hk
  have e : k.val = lw a := of_decide_eq_true hk
  show decide (k.val ∈ P.image pw ∪ Y.image lw) = true
  rw [decide_eq_true_eq, e]
  exact Finset.mem_union_right _ (Finset.mem_image_of_mem lw ha)

theorem snd (n N M : ℕ) (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop)
    (C : Circuit) (hC : IsAO2 n C)
    (hsound : ∀ (P : Finset (Fin N)) (Y : Finset (Fin M)), P.card ≤ 1 → Y.card ≤ 2 →
      (∀ p3 ∈ P, ∀ l3 ∈ Y, ¬ I p3 l3) →
      circuitFun n C (fun k : Fin n => decide (k.val ∈ P.image pw ∪ Y.image lw)) = false)
    (A B D : ℕ)
    (hout : ∀ x : Fin n → Bool, val C.gates A x = true → val C.gates B x = true →
      val C.gates D x = true → val C.gates C.output x = true)
    (a : Fin N) (m m2 : Fin M) (ha : a ∈ sh n C pw A) (hm : m ∈ sh n C lw B)
    (hm2 : m2 ∈ sh n C lw D) : I a m ∨ I a m2 := by
  by_contra hno
  rw [not_or] at hno
  have hs := hsound {a} {m, m2} (by simp) Finset.card_le_two (by
    intro p3 hp3 l3 hl3
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp3 hl3
    rcases hl3 with f | f
    · rw [hp3, f]
      exact hno.1
    · rw [hp3, f]
      exact hno.2)
  have ht : val C.gates C.output (xin n pw lw {a} {m, m2}) = true :=
    hout _ (up_p n C hC pw lw _ _ a (Finset.mem_singleton_self a) A ((mem_sh n C pw A a).1 ha))
      (up_l n C hC pw lw _ _ m (Finset.mem_insert_self m _) B ((mem_sh n C lw B m).1 hm))
      (up_l n C hC pw lw _ _ m2 (Finset.mem_insert_of_mem (Finset.mem_singleton_self m2)) D
        ((mem_sh n C lw D m2).1 hm2))
  have hs2 : val C.gates C.output (xin n pw lw {a} {m, m2}) = false := hs
  rw [ht] at hs2
  exact Bool.noConfusion hs2

theorem sh_input (n : ℕ) (C : Circuit) {K : ℕ} (f : Fin K → ℕ) (hf : Function.Injective f)
    (hn : ∀ a, f a < n) (p : Fin K) : sh n C f (f p) = {p} := by
  ext a
  rw [mem_sh, val_input C.gates _ _ (hn p)]
  show decide (f p = f a) = true ↔ _
  rw [decide_eq_true_eq, Set.mem_singleton_iff]
  constructor
  · intro h
    exact (hf h).symm
  · intro h
    rw [h]

theorem sh_orIn (n : ℕ) (C : Circuit) {K : ℕ} (f : Fin K → ℕ) (a : Fin K) (w : ℕ)
    (h : ∃ i : Fin n, i.val = f a ∧ i ∈ orIn n C w) : a ∈ sh n C f w := by
  obtain ⟨i, hi, hin⟩ := h
  rw [mem_sh]
  refine orIn_up n C (xs n f a) w i hin ?_
  rw [val_input C.gates _ _ i.isLt]
  show decide (i.val = f a) = true
  exact decide_eq_true hi

theorem two_le {K : ℕ} (S : Set (Fin K)) (a : Fin K) (ha : a ∈ S) (hne : S ≠ {a}) :
    2 ≤ S.ncard := by
  have hex : ∃ b ∈ S, b ≠ a := by
    by_contra h
    push_neg at h
    exact hne (Set.eq_singleton_iff_unique_mem.2 ⟨ha, h⟩)
  obtain ⟨b, hb, hba⟩ := hex
  exact (Set.one_lt_ncard_iff (Set.toFinite S)).2 ⟨a, b, ha, hb, fun e => hba e.symm⟩

theorem t0 (n N M : ℕ) (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop)
    (C : Circuit) (p : Fin N) (l : Fin M) (hC : IsAO2 n C)
    (hpi : Function.Injective pw) (hli : Function.Injective lw)
    (hpn : ∀ a, pw a < n) (hln : ∀ a, lw a < n)
    (hsound : ∀ (P : Finset (Fin N)) (Y : Finset (Fin M)), P.card ≤ 1 → Y.card ≤ 2 →
      (∀ p3 ∈ P, ∀ l3 ∈ Y, ¬ I p3 l3) →
      circuitFun n C (fun k : Fin n => decide (k.val ∈ P.image pw ∪ Y.image lw)) = false)
    (j K F : ℕ) (hj : IsAnd C j K F)
    (hK : ∃ i : Fin n, i.val = pw p ∧ i ∈ orIn n C K)
    (hF : ∃ i : Fin n, i.val = lw l ∧ i ∈ orIn n C F)
    (hout : OrReaches n C C.output j) : Concl n pw lw I C p l := by
  unfold Concl
  have hpK : p ∈ sh n C pw K := sh_orIn n C pw p K hK
  have hlF : l ∈ sh n C lw F := sh_orIn n C lw l F hF
  have ho : ∀ x : Fin n → Bool, val C.gates K x = true → val C.gates F x = true →
      val C.gates F x = true → val C.gates C.output x = true := by
    intro x hk hf _
    exact reach_up n C x j _ hout ((and_iff n C hC x j K F hj).2 ⟨hk, hf⟩)
  have key := fun a m m2 => snd n N M pw lw I C hC hsound K F F ho a m m2
  have hKs : sh n C pw K ⊆ {m | I m l} := fun a ha => (key a l l ha hlF hlF).elim id id
  have hFs : sh n C lw F ⊆ {m | I p m} := fun m hm => (key p m m hpK hm hm).elim id id
  by_cases h1 : sh n C pw K = {p}
  · by_cases h2 : sh n C lw F = {l}
    · exact Or.inr (Or.inr (Or.inl ⟨j, K, F, hj, h1, h2⟩))
    · exact Or.inl ⟨lw l, F, Or.inl hF, sh_input n C lw hli hln l, hFs, two_le _ l hlF h2⟩
  · exact Or.inr (Or.inl ⟨pw p, K, Or.inl hK, sh_input n C pw hpi hpn p, hKs,
      two_le _ p hpK h1⟩)

theorem t1 (n N M : ℕ) (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop)
    (C : Circuit) (p : Fin N) (l : Fin M) (hC : IsAO2 n C)
    (hpi : Function.Injective pw) (hli : Function.Injective lw)
    (hpn : ∀ a, pw a < n) (hln : ∀ a, lw a < n)
    (hsound : ∀ (P : Finset (Fin N)) (Y : Finset (Fin M)), P.card ≤ 1 → Y.card ≤ 2 →
      (∀ p3 ∈ P, ∀ l3 ∈ Y, ¬ I p3 l3) →
      circuitFun n C (fun k : Fin n => decide (k.val ∈ P.image pw ∪ Y.image lw)) = false)
    (j2 j3 K F2 V F3 : ℕ) (hj2 : IsAnd C j2 K F2)
    (hK : ∃ i : Fin n, i.val = pw p ∧ i ∈ orIn n C K)
    (hF2 : ∃ i : Fin n, i.val = lw l ∧ i ∈ orIn n C F2)
    (hV : OrReaches n C V j2) (hj3 : IsAnd C j3 V F3)
    (hF3 : ∃ i : Fin n, i.val = lw l ∧ i ∈ orIn n C F3)
    (hout : OrReaches n C C.output j3) : Concl n pw lw I C p l := by
  unfold Concl
  have hpK : p ∈ sh n C pw K := sh_orIn n C pw p K hK
  have hl2 : l ∈ sh n C lw F2 := sh_orIn n C lw l F2 hF2
  have hl3 : l ∈ sh n C lw F3 := sh_orIn n C lw l F3 hF3
  have ho : ∀ x : Fin n → Bool, val C.gates K x = true → val C.gates F2 x = true →
      val C.gates F3 x = true → val C.gates C.output x = true := by
    intro x hk hf2 hf3
    exact reach_up n C x j3 _ hout ((and_iff n C hC x j3 V F3 hj3).2
      ⟨reach_up n C x j2 V hV ((and_iff n C hC x j2 K F2 hj2).2 ⟨hk, hf2⟩), hf3⟩)
  have key := fun a m m2 => snd n N M pw lw I C hC hsound K F2 F3 ho a m m2
  have hKs : sh n C pw K ⊆ {m | I m l} := fun a ha => (key a l l ha hl2 hl3).elim id id
  by_cases h1 : sh n C pw K = {p}
  · by_cases h2 : sh n C lw F2 = {l}
    · exact Or.inr (Or.inr (Or.inl ⟨j2, K, F2, hj2, h1, h2⟩))
    · by_cases h3 : sh n C lw F2 ⊆ {m | I p m}
      · exact Or.inl ⟨lw l, F2, Or.inl hF2, sh_input n C lw hli hln l, h3, two_le _ l hl2 h2⟩
      · obtain ⟨m3, hm3, hnm⟩ := Set.not_subset.1 h3
        have hF3s : sh n C lw F3 ⊆ {m | I p m} := fun m hm =>
          (key p m3 m hpK hm3 hm).elim (fun h => (hnm h).elim) id
        by_cases h4 : sh n C lw F3 = {l}
        · exact Or.inr (Or.inr (Or.inr ⟨j2, K, F2, V, j3, F3, m3, hj2, h1, hm3, hnm, hV, hj3,
            h4, hout⟩))
        · exact Or.inl ⟨lw l, F3, Or.inl hF3, sh_input n C lw hli hln l, hF3s,
            two_le _ l hl3 h4⟩
  · exact Or.inr (Or.inl ⟨pw p, K, Or.inl hK, sh_input n C pw hpi hpn p, hKs,
      two_le _ p hpK h1⟩)

theorem t2 (n N M : ℕ) (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop)
    (C : Circuit) (p : Fin N) (l : Fin M) (hC : IsAO2 n C)
    (hpi : Function.Injective pw) (hli : Function.Injective lw)
    (hpn : ∀ a, pw a < n) (hln : ∀ a, lw a < n)
    (hsound : ∀ (P : Finset (Fin N)) (Y : Finset (Fin M)), P.card ≤ 1 → Y.card ≤ 2 →
      (∀ p3 ∈ P, ∀ l3 ∈ Y, ¬ I p3 l3) →
      circuitFun n C (fun k : Fin n => decide (k.val ∈ P.image pw ∪ Y.image lw)) = false)
    (j4 j5 F4 F5 U K : ℕ) (hj4 : IsAnd C j4 F4 F5)
    (hF4 : ∃ i : Fin n, i.val = lw l ∧ i ∈ orIn n C F4)
    (hF5 : ∃ i : Fin n, i.val = lw l ∧ i ∈ orIn n C F5)
    (hU : OrReaches n C U j4) (hj5 : IsAnd C j5 K U)
    (hK : ∃ i : Fin n, i.val = pw p ∧ i ∈ orIn n C K)
    (hout : OrReaches n C C.output j5) : Concl n pw lw I C p l := by
  unfold Concl
  have hpK : p ∈ sh n C pw K := sh_orIn n C pw p K hK
  have hl4 : l ∈ sh n C lw F4 := sh_orIn n C lw l F4 hF4
  have hl5 : l ∈ sh n C lw F5 := sh_orIn n C lw l F5 hF5
  have ho : ∀ x : Fin n → Bool, val C.gates K x = true → val C.gates F4 x = true →
      val C.gates F5 x = true → val C.gates C.output x = true := by
    intro x hk h4 h5
    exact reach_up n C x j5 _ hout ((and_iff n C hC x j5 K U hj5).2
      ⟨hk, reach_up n C x j4 U hU ((and_iff n C hC x j4 F4 F5 hj4).2 ⟨h4, h5⟩)⟩)
  have ho2 : ∀ x : Fin n → Bool, val C.gates K x = true → val C.gates U x = true →
      val C.gates U x = true → val C.gates C.output x = true := by
    intro x hk hu _
    exact reach_up n C x j5 _ hout ((and_iff n C hC x j5 K U hj5).2 ⟨hk, hu⟩)
  have key := fun a m m2 => snd n N M pw lw I C hC hsound K F4 F5 ho a m m2
  have key2 := fun a m m2 => snd n N M pw lw I C hC hsound K U U ho2 a m m2
  have hlg : l ∈ sh n C lw (n + j4) :=
    (mem_sh n C lw (n + j4) l).2 ((and_iff n C hC (xs n lw l) j4 F4 F5 hj4).2
      ⟨(mem_sh n C lw F4 l).1 hl4, (mem_sh n C lw F5 l).1 hl5⟩)
  have hgU : sh n C lw (n + j4) ⊆ sh n C lw U := fun m hm =>
    (mem_sh n C lw U m).2 (reach_up n C (xs n lw m) j4 U hU ((mem_sh n C lw (n + j4) m).1 hm))
  have hg4 : sh n C lw (n + j4) ⊆ sh n C lw F4 := fun m hm =>
    (mem_sh n C lw F4 m).2
      ((and_iff n C hC (xs n lw m) j4 F4 F5 hj4).1 ((mem_sh n C lw (n + j4) m).1 hm)).1
  have hg5 : sh n C lw (n + j4) ⊆ sh n C lw F5 := fun m hm =>
    (mem_sh n C lw F5 m).2
      ((and_iff n C hC (xs n lw m) j4 F4 F5 hj4).1 ((mem_sh n C lw (n + j4) m).1 hm)).2
  have hKs : sh n C pw K ⊆ {m | I m l} := fun a ha => (key a l l ha hl4 hl5).elim id id
  have hUs : sh n C lw U ⊆ {m | I p m} := fun m hm => (key2 p m m hpK hm hm).elim id id
  have hlU : l ∈ sh n C lw U := hgU hlg
  by_cases h1 : sh n C pw K = {p}
  · by_cases h2 : sh n C lw U = {l}
    · exact Or.inr (Or.inr (Or.inl ⟨j5, K, U, hj5, h1, h2⟩))
    · by_cases h3 : sh n C lw (n + j4) = {l}
      · exact Or.inl ⟨n + j4, U, Or.inr ⟨j4, rfl, hU⟩, h3, hUs, two_le _ l hlU h2⟩
      · by_cases h4 : sh n C lw F4 ⊆ {m | I p m}
        · exact Or.inl ⟨lw l, F4, Or.inl hF4, sh_input n C lw hli hln l, h4,
            le_trans (two_le _ l hlg h3) (Set.ncard_le_ncard hg4 (Set.toFinite _))⟩
        · obtain ⟨m3, hm3, hnm⟩ := Set.not_subset.1 h4
          have h5s : sh n C lw F5 ⊆ {m | I p m} := fun m hm =>
            (key p m3 m hpK hm3 hm).elim (fun h => (hnm h).elim) id
          exact Or.inl ⟨lw l, F5, Or.inl hF5, sh_input n C lw hli hln l, h5s,
            le_trans (two_le _ l hlg h3) (Set.ncard_le_ncard hg5 (Set.toFinite _))⟩
  · exact Or.inr (Or.inl ⟨pw p, K, Or.inl hK, sh_input n C pw hpi hpn p, hKs,
      two_le _ p hpK h1⟩)

end PEqualNP.Outside.L_meta_2485

theorem PEqualNP.Outside.L_meta_2485 : ∀ (n N M : ℕ) (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop) (C : PEqualNP.CircuitLowerBounds.Circuit) (p : Fin N) (l : Fin M), PEqualNP.TopForm.IsAO2 n C → (Function.Injective pw ∧ Function.Injective lw ∧ (∀ p_1 l_1, pw p_1 ≠ lw l_1) ∧ (∀ p_2, pw p_2 < n) ∧ (∀ l_2, lw l_2 < n)) → (∀ (P_1 : Finset (Fin N)) (Y_1 : Finset (Fin M)), P_1.card ≤ 1 → Y_1.card ≤ 2 → (∀ p_3 ∈ P_1, ∀ l_3 ∈ Y_1, ¬ I p_3 l_3) → PEqualNP.MetaComplexity.circuitFun n C (fun k_1 : Fin n => decide (k_1.val ∈ P_1.image pw ∪ Y_1.image lw)) = false) → I p l → ((∃ j_1 K_1 F_1, (j_1 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_1).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j_1).inputs = [K_1, F_1] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_1).inputs = [F_1, K_1])) ∧ (∃ i_1 : Fin n, i_1.val = pw p ∧ i_1 ∈ PEqualNP.TopForm.orIn n C (K_1)) ∧ (∃ i_2 : Fin n, i_2.val = lw l ∧ i_2 ∈ PEqualNP.TopForm.orIn n C (F_1)) ∧ PEqualNP.CleanedNonEdge.OrReaches n C (C.output) j_1) ∨ (∃ j_2 j_3 K_2 F_2 V_1 F_3, (j_2 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_2).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j_2).inputs = [K_2, F_2] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_2).inputs = [F_2, K_2])) ∧ (∃ i_3 : Fin n, i_3.val = pw p ∧ i_3 ∈ PEqualNP.TopForm.orIn n C (K_2)) ∧ (∃ i_4 : Fin n, i_4.val = lw l ∧ i_4 ∈ PEqualNP.TopForm.orIn n C (F_2)) ∧ PEqualNP.CleanedNonEdge.OrReaches n C (V_1) j_2 ∧ (j_3 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_3).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j_3).inputs = [V_1, F_3] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_3).inputs = [F_3, V_1])) ∧ (∃ i_5 : Fin n, i_5.val = lw l ∧ i_5 ∈ PEqualNP.TopForm.orIn n C (F_3)) ∧ PEqualNP.CleanedNonEdge.OrReaches n C (C.output) j_3) ∨ (∃ j_4 j_5 F_4 F_5 U_1 K_3, (j_4 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_4).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j_4).inputs = [F_4, F_5] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_4).inputs = [F_5, F_4])) ∧ (∃ i_6 : Fin n, i_6.val = lw l ∧ i_6 ∈ PEqualNP.TopForm.orIn n C (F_4)) ∧ (∃ i_7 : Fin n, i_7.val = lw l ∧ i_7 ∈ PEqualNP.TopForm.orIn n C (F_5)) ∧ PEqualNP.CleanedNonEdge.OrReaches n C (U_1) j_4 ∧ (j_5 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_5).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j_5).inputs = [K_3, U_1] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_5).inputs = [U_1, K_3])) ∧ (∃ i_8 : Fin n, i_8.val = pw p ∧ i_8 ∈ PEqualNP.TopForm.orIn n C (K_3)) ∧ PEqualNP.CleanedNonEdge.OrReaches n C (C.output) j_5)) → (∃ a_1 F_6, ((∃ i_9 : Fin n, i_9.val = a_1 ∧ i_9 ∈ PEqualNP.TopForm.orIn n C (F_6)) ∨ (∃ j_6 : ℕ, a_1 = n + j_6 ∧ PEqualNP.CleanedNonEdge.OrReaches n C (F_6) j_6)) ∧ {a_3 | PEqualNP.CleanedNonEdge.wireVal n C (a_1) (fun k_3 : Fin n => decide (k_3.val = lw a_3)) = true} = {l} ∧ {a_2 | PEqualNP.CleanedNonEdge.wireVal n C (F_6) (fun k_2 : Fin n => decide (k_2.val = lw a_2)) = true} ⊆ {m_1 | I p m_1} ∧ 2 ≤ ({a_4 | PEqualNP.CleanedNonEdge.wireVal n C (F_6) (fun k_4 : Fin n => decide (k_4.val = lw a_4)) = true}).ncard) ∨ (∃ a_5 F_7, ((∃ i_10 : Fin n, i_10.val = a_5 ∧ i_10 ∈ PEqualNP.TopForm.orIn n C (F_7)) ∨ (∃ j_7 : ℕ, a_5 = n + j_7 ∧ PEqualNP.CleanedNonEdge.OrReaches n C (F_7) j_7)) ∧ {a_7 | PEqualNP.CleanedNonEdge.wireVal n C (a_5) (fun k_6 : Fin n => decide (k_6.val = pw a_7)) = true} = {p} ∧ {a_6 | PEqualNP.CleanedNonEdge.wireVal n C (F_7) (fun k_5 : Fin n => decide (k_5.val = pw a_6)) = true} ⊆ {m_2 | I m_2 l} ∧ 2 ≤ ({a_8 | PEqualNP.CleanedNonEdge.wireVal n C (F_7) (fun k_7 : Fin n => decide (k_7.val = pw a_8)) = true}).ncard) ∨ (∃ j_8 a_9 b_1, (j_8 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_8).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j_8).inputs = [a_9, b_1] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_8).inputs = [b_1, a_9])) ∧ {a_10 | PEqualNP.CleanedNonEdge.wireVal n C (a_9) (fun k_8 : Fin n => decide (k_8.val = pw a_10)) = true} = {p} ∧ {a_11 | PEqualNP.CleanedNonEdge.wireVal n C (b_1) (fun k_9 : Fin n => decide (k_9.val = lw a_11)) = true} = {l}) ∨ (∃ j_9 K_4 F_8 V_2 j_10 F_9 m_3, (j_9 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_9).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j_9).inputs = [K_4, F_8] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_9).inputs = [F_8, K_4])) ∧ {a_12 | PEqualNP.CleanedNonEdge.wireVal n C (K_4) (fun k_10 : Fin n => decide (k_10.val = pw a_12)) = true} = {p} ∧ m_3 ∈ {a_13 | PEqualNP.CleanedNonEdge.wireVal n C (F_8) (fun k_11 : Fin n => decide (k_11.val = lw a_13)) = true} ∧ ¬ I p m_3 ∧ PEqualNP.CleanedNonEdge.OrReaches n C (V_2) j_9 ∧ (j_10 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_10).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j_10).inputs = [V_2, F_9] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_10).inputs = [F_9, V_2])) ∧ {a_14 | PEqualNP.CleanedNonEdge.wireVal n C (F_9) (fun k_12 : Fin n => decide (k_12.val = lw a_14)) = true} = {l} ∧ PEqualNP.CleanedNonEdge.OrReaches n C (C.output) j_10) := by
  intro n N M pw lw I C p l hC hw hsound _ hcert
  obtain ⟨hpi, hli, _, hpn, hln⟩ := hw
  rcases hcert with ⟨j1, K1, F1, hj, hK, hF, hout⟩ | ⟨j2, j3, K2, F2, V1, F3, hj2, hK, hF2, hV, hj3, hF3, hout⟩ | ⟨j4, j5, F4, F5, U1, K3, hj4, hF4, hF5, hU, hj5, hK, hout⟩
  · exact PEqualNP.Outside.L_meta_2485.t0 n N M pw lw I C p l hC hpi hli hpn hln hsound j1 K1 F1 hj hK hF hout
  · exact PEqualNP.Outside.L_meta_2485.t1 n N M pw lw I C p l hC hpi hli hpn hln hsound j2 j3 K2 F2 V1 F3 hj2 hK hF2 hV hj3 hF3 hout
  · exact PEqualNP.Outside.L_meta_2485.t2 n N M pw lw I C p l hC hpi hli hpn hln hsound j4 j5 F4 F5 U1 K3 hj4 hF4 hF5 hU hj5 hK hout
