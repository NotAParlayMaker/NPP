import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2489


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

theorem dirty_on (n N M : ℕ) (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop) (C : Circuit)
    (l : Fin M) (h V F2 j2 : ℕ) (hC : IsAO2 n C)
    (hS : ∀ (P_1 : Finset (Fin N)) (Y_1 : Finset (Fin M)), P_1.card ≤ 1 → Y_1.card ≤ 2 →
      (∀ p_3 ∈ P_1, ∀ l_3 ∈ Y_1, ¬ I p_3 l_3) →
      circuitFun n C (fun k_1 : Fin n => decide (k_1.val ∈ P_1.image pw ∪ Y_1.image lw)) = false)
    (hV : (∃ i_1 : Fin n, i_1.val = h ∧ i_1 ∈ orIn n C V) ∨
      (∃ j_1 : ℕ, h = n + j_1 ∧ OrReaches n C V j_1))
    (hj : j2 < C.gates.length) (hop : (gateAt C j2).op = GateOp.and)
    (hin : (gateAt C j2).inputs = [V, F2] ∨ (gateAt C j2).inputs = [F2, V])
    (hout : OrReaches n C C.output j2)
    (hl : wireVal n C F2 (fun k_2 : Fin n => decide (k_2.val = lw l)) = true)
    (p : Fin N) (m1 : Fin M) (hnI : ¬ I p m1)
    (hw : wireVal n C h (fun k_3 : Fin n => decide (k_3.val ∈ ({pw p, lw m1} : Finset ℕ))) = true) :
    I p l := by
  by_contra hn
  have hz := hS {p} {m1, l} (by simp) Finset.card_le_two (by
    intro a ha b hb
    rw [Finset.mem_singleton] at ha
    rw [Finset.mem_insert, Finset.mem_singleton] at hb
    rw [ha]
    rcases hb with hb | hb
    · rw [hb]; exact hnI
    · rw [hb]; exact hn)
  have h1 : wireVal n C h (fun k : Fin n => decide (k.val ∈ ({p} : Finset (Fin N)).image pw ∪
      ({m1, l} : Finset (Fin M)).image lw)) = true := by
    refine wires_mono C hC.1
      (fun k_3 : Fin n => decide (k_3.val ∈ ({pw p, lw m1} : Finset ℕ)))
      (fun k : Fin n => decide (k.val ∈ ({p} : Finset (Fin N)).image pw ∪
        ({m1, l} : Finset (Fin M)).image lw)) ?_ h hw
    intro k hk
    have hk2 := of_decide_eq_true hk
    apply decide_eq_true
    rw [Finset.mem_insert, Finset.mem_singleton] at hk2
    rcases hk2 with e | e
    · rw [e]
      exact Finset.mem_union_left _ (Finset.mem_image_of_mem pw (Finset.mem_singleton_self p))
    · rw [e]
      exact Finset.mem_union_right _ (Finset.mem_image_of_mem lw (Finset.mem_insert_self _ _))
  have h2 : wireVal n C F2 (fun k : Fin n => decide (k.val ∈ ({p} : Finset (Fin N)).image pw ∪
      ({m1, l} : Finset (Fin M)).image lw)) = true := by
    refine wires_mono C hC.1
      (fun k_2 : Fin n => decide (k_2.val = lw l))
      (fun k : Fin n => decide (k.val ∈ ({p} : Finset (Fin N)).image pw ∪
        ({m1, l} : Finset (Fin M)).image lw)) ?_ F2 hl
    intro k hk
    have hk2 := of_decide_eq_true hk
    apply decide_eq_true
    rw [hk2]
    exact Finset.mem_union_right _ (Finset.mem_image_of_mem lw
      (Finset.mem_insert_of_mem (Finset.mem_singleton_self l)))
  rw [wires_eq] at h1 h2
  have h3 := or_up n C _ h V hV h1
  have h4 : val C.gates (n + j2) (fun k : Fin n => decide (k.val ∈ ({p} : Finset (Fin N)).image pw ∪
      ({m1, l} : Finset (Fin M)).image lw)) = true := by
    rw [and_eq n C hC _ j2 hj hop]
    rcases hin with e | e
    · rw [e]
      simp only [List.getD_cons_zero, List.getD_cons_succ]
      rw [Bool.and_eq_true]
      exact ⟨h3, h2⟩
    · rw [e]
      simp only [List.getD_cons_zero, List.getD_cons_succ]
      rw [Bool.and_eq_true]
      exact ⟨h2, h3⟩
  have h5 := reach_up n C _ j2 C.output hout h4
  have h6 : circuitFun n C (fun k : Fin n => decide (k.val ∈ ({p} : Finset (Fin N)).image pw ∪
      ({m1, l} : Finset (Fin M)).image lw)) = true := h5
  rw [hz] at h6
  exact Bool.false_ne_true h6


theorem in_two {l : List ℕ} (hl : l.length = 2) {w : ℕ} (hw : w ∈ l) :
    w = l.getD 0 0 ∨ w = l.getD 1 0 := by
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩
  · simp at hl
  · simp at hl
  · simp at hw ⊢
    exact hw
  · simp at hl

theorem gate_mem (C : Circuit) {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  unfold gateAt
  rw [List.getD_eq_getElem _ _ hj]
  exact List.getElem_mem hj


theorem walk (n : ℕ) (C : Circuit) (hlen : ∀ g ∈ C.gates, g.inputs.length = 2) (Q : ℕ → Prop)
    (j : ℕ) :
    ∀ b : ℕ, OrReaches n C b j → Q (n + j) → ¬ Q b →
      ∃ k, ∃ c : Bool, k < C.gates.length ∧ (gateAt C k).op = GateOp.or ∧
        (gateAt C k).inputs.getD (cond c 1 0) 0 ∈ (gateAt C k).inputs ∧
        Q ((gateAt C k).inputs.getD (cond c 1 0) 0) ∧ ¬ Q (n + k) ∧ OrReaches n C b k := by
  intro b
  induction b using Nat.strong_induction_on with
  | _ b ih =>
    intro h hQ hnQ
    have hnb : n ≤ b := h.1
    obtain ⟨k, hbk⟩ : ∃ k, b = n + k := ⟨b - n, by omega⟩
    rw [hbk] at h hnQ ⊢
    obtain ⟨hk, h3⟩ := (orReaches_iff n C k j).1 h
    rcases h3 with h3 | ⟨hop, i, hi, hlt, hr⟩
    · rw [h3] at hQ
      exact absurd hQ hnQ
    · have hself : OrReaches n C (n + k) k := (orReaches_iff n C k k).2 ⟨hk, Or.inl rfl⟩
      by_cases hQi : Q i
      · rcases in_two (hlen _ (gate_mem C hk)) hi with h2 | h2
        · rw [h2] at hi hQi
          exact ⟨k, false, hk, hop, hi, hQi, hnQ, hself⟩
        · rw [h2] at hi hQi
          exact ⟨k, true, hk, hop, hi, hQi, hnQ, hself⟩
      · obtain ⟨k2, c, hk2, hop2, hin2, hQ2, hnQ2, hr2⟩ := ih i (by omega) hr hQ hQi
        exact ⟨k2, c, hk2, hop2, hin2, hQ2, hnQ2,
          (orReaches_iff n C k k2).2 ⟨hk, Or.inr ⟨hop, i, hi, hlt, hr2⟩⟩⟩



section Sec2487

namespace P2487


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def G {α : Type} (src : α → ℕ) (seg : α → ℕ → Prop) (D : ℕ → Finset α) (isOr : ℕ → Prop)
    (g0 g1 : ℕ → ℕ) (p : α) (y x : ℕ) : Prop :=
  seg p y ∧ 2 ≤ (D y).card ∧
    (y = src p ∨ (seg p x ∧ (D x).card < 2 ∧ isOr y ∧ (g0 y = x ∨ g1 y = x)))

theorem core {α : Type} (Pl : Finset α) (src top : α → ℕ) (seg : α → ℕ → Prop)
    (D : ℕ → Finset α) (L : ℕ) (isOr : ℕ → Prop) (g0 g1 : ℕ → ℕ)
    (h1 : ∀ p ∈ Pl, seg p (src p) ∧ seg p (top p) ∧ ¬ isOr (src p))
    (h2 : ∀ p ∈ Pl, ∀ x, seg p x → p ∈ D x ∧ x < L)
    (h3 : ∀ p ∈ Pl, ∀ x, seg p x → x ≠ top p →
      ∃ y, isOr y ∧ (g0 y = x ∨ g1 y = x) ∧ seg p y ∧ D x ⊆ D y ∧ x < y)
    (h4 : ∀ g : ℕ, (Pl.filter (fun p => src p = g)).card ≤ 2)
    (W : Finset ℕ) (mem_W : ∀ x, x ∈ W ↔ ∃ p ∈ Pl, seg p x ∧ 2 ≤ (D x).card) :
    Pl.card ≤ W.card + (Pl.image top).card := by
  classical
  have stepA : ∀ p ∈ Pl, ∀ k x, L - x ≤ k → seg p x → (D x).card < 2 →
      (∃ y x1, seg p y ∧ 2 ≤ (D y).card ∧ seg p x1 ∧ (D x1).card < 2 ∧ isOr y ∧
        (g0 y = x1 ∨ g1 y = x1)) ∨ (D (top p)).card < 2 := by
    intro p hp k
    induction k with
    | zero =>
      intro x hk hs _
      have := (h2 p hp x hs).2
      omega
    | succ k ih =>
      intro x hk hs hn
      by_cases hxt : x = top p
      · right
        rw [← hxt]
        exact hn
      · obtain ⟨y, hyo, hys, hsy, _, hxy⟩ := h3 p hp x hs hxt
        by_cases hwy : 2 ≤ (D y).card
        · exact Or.inl ⟨y, x, hsy, hwy, hs, hn, hyo, hys⟩
        · exact ih y (by omega) hsy (by omega)
  have stepB : ∀ p ∈ Pl, (∃ y x, G src seg D isOr g0 g1 p y x) ∨ (D (top p)).card < 2 := by
    intro p hp
    obtain ⟨hs, _, _⟩ := h1 p hp
    by_cases hw : 2 ≤ (D (src p)).card
    · exact Or.inl ⟨src p, 0, hs, hw, Or.inl rfl⟩
    · rcases stepA p hp (L - src p) (src p) le_rfl hs (by omega) with ⟨y, x, a, b, c, d, e, f⟩ | h
      · exact Or.inl ⟨y, x, a, b, Or.inr ⟨c, d, e, f⟩⟩
      · exact Or.inr h
  obtain ⟨P2, P1, hsum, mem_P2, mem_P1⟩ : ∃ P2 P1 : Finset α, P2.card + P1.card = Pl.card ∧
      (∀ p, p ∈ P2 ↔ p ∈ Pl ∧ ∃ y x, G src seg D isOr g0 g1 p y x) ∧
      (∀ p, p ∈ P1 ↔ p ∈ Pl ∧ ¬ ∃ y x, G src seg D isOr g0 g1 p y x) :=
    ⟨_, _, Finset.card_filter_add_card_filter_not (s := Pl)
      (fun p => ∃ y x, G src seg D isOr g0 g1 p y x),
      fun p => Finset.mem_filter, fun p => Finset.mem_filter⟩
  have hG : ∀ p ∈ P2, ∃ y x, G src seg D isOr g0 g1 p y x := fun p hp => ((mem_P2 p).mp hp).2
  choose! m px hm using hG
  have hP2Pl : ∀ p ∈ P2, p ∈ Pl := fun p hp => ((mem_P2 p).mp hp).1
  have hfib : ∀ p ∈ P2, isOr (m p) →
      seg p (px p) ∧ (D (px p)).card < 2 ∧ (g0 (m p) = px p ∨ g1 (m p) = px p) := by
    intro p hp ho
    obtain ⟨_, _, h | ⟨a, b, _, d⟩⟩ := hm p hp
    · rw [h] at ho
      exact absurd ho (h1 p (hP2Pl p hp)).2.2
    · exact ⟨a, b, d⟩
  have hsrc : ∀ p ∈ P2, ¬ isOr (m p) → m p = src p := by
    intro p hp ho
    obtain ⟨_, _, h | ⟨_, _, c, _⟩⟩ := hm p hp
    · exact h
    · exact absurd c ho
  have hmW : ∀ p ∈ P2, m p ∈ W := by
    intro p hp
    obtain ⟨hs, hw, _⟩ := hm p hp
    exact (mem_W _).mpr ⟨p, hP2Pl p hp, hs, hw⟩
  have hpar : ∀ y ∈ W \ Pl.image top, ∃ z, z ∈ W ∧ isOr z ∧ (g0 z = y ∨ g1 z = y) := by
    intro y hy
    rw [Finset.mem_sdiff] at hy
    obtain ⟨p, hp, hs, hw⟩ := (mem_W y).mp hy.1
    have hne : y ≠ top p := by
      intro h
      apply hy.2
      rw [h]
      exact Finset.mem_image_of_mem top hp
    obtain ⟨z, hzo, hzs, hsz, hD, _⟩ := h3 p hp y hs hne
    exact ⟨z, (mem_W z).mpr ⟨p, hp, hsz, le_trans hw (Finset.card_le_card hD)⟩, hzo, hzs⟩
  choose! par hpar1 using hpar
  have hwide : ∀ y ∈ W \ Pl.image top, 2 ≤ (D y).card := by
    intro y hy
    rw [Finset.mem_sdiff] at hy
    obtain ⟨_, _, _, hw⟩ := (mem_W y).mp hy.1
    exact hw
  have hnar : ∀ p ∈ P1, (D (top p)).card < 2 := by
    intro p hp
    have hp1 := (mem_P1 p).mp hp
    rcases stepB p hp1.1 with h | h
    · exact absurd h hp1.2
    · exact h
  have hP1c : P1.card ≤ (Pl.image top \ W).card := by
    apply Finset.card_le_card_of_injOn top
    · intro p hp
      have hp0 : p ∈ P1 := Finset.mem_coe.mp hp
      have hp1 := (mem_P1 p).mp hp0
      have hn := hnar p hp0
      refine Finset.mem_coe.mpr (Finset.mem_sdiff.mpr ⟨Finset.mem_image_of_mem top hp1.1, ?_⟩)
      intro hw
      obtain ⟨_, _, _, hw2⟩ := (mem_W _).mp hw
      omega
    · intro p hp q hq hpq
      have hp0 : p ∈ P1 := Finset.mem_coe.mp hp
      have hq0 : q ∈ P1 := Finset.mem_coe.mp hq
      have hp1 := (mem_P1 p).mp hp0
      have hq1 := (mem_P1 q).mp hq0
      have hn := hnar p hp0
      have h1p := (h2 p hp1.1 (top p) (h1 p hp1.1).2.1).1
      have h1q := (h2 q hq1.1 (top q) (h1 q hq1.1).2.1).1
      rw [← hpq] at h1q
      exact Finset.card_le_one.mp (by omega) p h1p q h1q
  have hQ : (P2.disjSum (W \ Pl.image top)).card ≤ 2 * W.card := by
    refine Finset.card_le_mul_card_image_of_maps_to (f := Sum.elim m par) ?_ 2 ?_
    · intro q hq
      rcases Finset.mem_disjSum.mp hq with ⟨p, hp, rfl⟩ | ⟨y, hy, rfl⟩
      · exact hmW p hp
      · exact (hpar1 y hy).1
    · intro y hy
      by_cases hyo : isOr y
      · refine le_trans (Finset.card_le_card_of_injOn (t := ({g0 y, g1 y} : Finset ℕ))
          (Sum.elim px id) ?_ ?_) Finset.card_le_two
        · intro q hq
          obtain ⟨hq1, hq2⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hq)
          rcases Finset.mem_disjSum.mp hq1 with ⟨p, hp, rfl⟩ | ⟨z, hz, rfl⟩
          · have hq3 : m p = y := hq2
            obtain ⟨_, _, hsl⟩ := hfib p hp (by rw [hq3]; exact hyo)
            rw [hq3] at hsl
            refine Finset.mem_coe.mpr ?_
            show px p ∈ ({g0 y, g1 y} : Finset ℕ)
            rw [Finset.mem_insert, Finset.mem_singleton]
            rcases hsl with h | h
            · exact Or.inl h.symm
            · exact Or.inr h.symm
          · have hq3 : par z = y := hq2
            have hsl := (hpar1 z hz).2.2
            rw [hq3] at hsl
            refine Finset.mem_coe.mpr ?_
            show z ∈ ({g0 y, g1 y} : Finset ℕ)
            rw [Finset.mem_insert, Finset.mem_singleton]
            rcases hsl with h | h
            · exact Or.inl h.symm
            · exact Or.inr h.symm
        · intro q hq q1 hq1 heq
          obtain ⟨hqa, hqb⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hq)
          obtain ⟨hq1a, hq1b⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hq1)
          rcases Finset.mem_disjSum.mp hqa with ⟨p, hp, rfl⟩ | ⟨z, hz, rfl⟩
          · have hq3 : m p = y := hqb
            obtain ⟨hsp, hnp, _⟩ := hfib p hp (by rw [hq3]; exact hyo)
            rcases Finset.mem_disjSum.mp hq1a with ⟨p1, hp1, rfl⟩ | ⟨z1, hz1, rfl⟩
            · have hq4 : m p1 = y := hq1b
              obtain ⟨hsp1, _, _⟩ := hfib p1 hp1 (by rw [hq4]; exact hyo)
              have he : px p = px p1 := heq
              have hd := (h2 p (hP2Pl p hp) _ hsp).1
              have hd1 := (h2 p1 (hP2Pl p1 hp1) _ hsp1).1
              rw [← he] at hd1
              have : p = p1 := Finset.card_le_one.mp (by omega) p hd p1 hd1
              rw [this]
            · have he : px p = z1 := heq
              have := hwide z1 hz1
              rw [← he] at this
              omega
          · rcases Finset.mem_disjSum.mp hq1a with ⟨p1, hp1, rfl⟩ | ⟨z1, hz1, rfl⟩
            · have hq4 : m p1 = y := hq1b
              obtain ⟨_, hnp1, _⟩ := hfib p1 hp1 (by rw [hq4]; exact hyo)
              have he : z = px p1 := heq
              have := hwide z hz
              rw [he] at this
              omega
            · have he : z = z1 := heq
              rw [he]
      · refine le_trans (Finset.card_le_card ?_)
          (le_trans (Finset.card_image_le (f := Sum.inl)) (h4 y))
        intro q hq
        obtain ⟨hq1, hq2⟩ := Finset.mem_filter.mp hq
        rcases Finset.mem_disjSum.mp hq1 with ⟨p, hp, rfl⟩ | ⟨z, hz, rfl⟩
        · have hq3 : m p = y := hq2
          refine Finset.mem_image.mpr ⟨p, Finset.mem_filter.mpr ⟨hP2Pl p hp, ?_⟩, rfl⟩
          rw [← hsrc p hp (by rw [hq3]; exact hyo)]
          exact hq3
        · have hq3 : par z = y := hq2
          have := (hpar1 z hz).2.1
          rw [hq3] at this
          exact absurd this hyo
  rw [Finset.card_disjSum] at hQ
  have e1 := Finset.card_sdiff_add_card_inter W (Pl.image top)
  have e2 := Finset.card_sdiff_add_card_inter (Pl.image top) W
  rw [Finset.inter_comm] at e2
  omega

theorem main (n N : ℕ) (C : Circuit) (Pl : Finset (Fin N)) (src top : Fin N → ℕ)
    (seg : Fin N → ℕ → Prop) (D : ℕ → Finset (Fin N)) (hAO : PEqualNP.TopForm.IsAO2 n C)
    (h1 : ∀ p ∈ Pl, seg p (src p) ∧ seg p (top p) ∧ ∃ j, src p = n + j ∧ j < C.gates.length ∧
      (gateAt C j).op = GateOp.and)
    (h2 : ∀ p2 ∈ Pl, ∀ x : ℕ, seg p2 x → p2 ∈ D x ∧ n ≤ x ∧ x < n + C.gates.length)
    (h3 : ∀ p3 ∈ Pl, ∀ x2 : ℕ, seg p3 x2 → x2 ≠ top p3 → ∃ j2 c, j2 < C.gates.length ∧
      (gateAt C j2).op = GateOp.or ∧ (gateAt C j2).inputs.getD c 0 = x2 ∧ c < 2 ∧
      seg p3 (n + j2) ∧ D x2 ⊆ D (n + j2))
    (h4 : ∀ g : ℕ, (Pl.filter (fun p4 => src p4 = g)).card ≤ 2) :
    Pl.card ≤ {x3 : ℕ | ∃ p5 ∈ Pl, seg p5 x3 ∧ 2 ≤ (D x3).card}.ncard + (Pl.image top).card := by
  have hfin : {x3 : ℕ | ∃ p5 ∈ Pl, seg p5 x3 ∧ 2 ≤ (D x3).card}.Finite :=
    (Set.finite_lt_nat (n + C.gates.length)).subset (fun x hx => by
      obtain ⟨p, hp, hs, _⟩ := hx
      exact (h2 p hp x hs).2.2)
  rw [Set.ncard_eq_toFinset_card _ hfin]
  refine core Pl src top seg D (n + C.gates.length)
    (fun y => ∃ j, y = n + j ∧ j < C.gates.length ∧ (gateAt C j).op = GateOp.or)
    (fun y => (gateAt C (y - n)).inputs.getD 0 0) (fun y => (gateAt C (y - n)).inputs.getD 1 0)
    ?_ ?_ ?_ h4 hfin.toFinset (fun x => hfin.mem_toFinset)
  · intro p hp
    obtain ⟨a, b, j, hj, hjl, hop⟩ := h1 p hp
    refine ⟨a, b, ?_⟩
    rintro ⟨j1, hj1, _, hop1⟩
    have hjj : j = j1 := by omega
    subst hjj
    rw [hop] at hop1
    cases hop1
  · intro p hp x hs
    exact ⟨(h2 p hp x hs).1, (h2 p hp x hs).2.2⟩
  · intro p hp x hs hne
    obtain ⟨j, c, hjl, hop, hc, hc2, hsj, hD⟩ := h3 p hp x hs hne
    refine ⟨n + j, ⟨j, rfl, hjl, hop⟩, ?_, hsj, hD, ?_⟩
    · show (gateAt C (n + j - n)).inputs.getD 0 0 = x ∨ (gateAt C (n + j - n)).inputs.getD 1 0 = x
      rw [Nat.add_sub_cancel_left]
      rcases (by omega : c = 0 ∨ c = 1) with hc0 | hc0
      · rw [hc0] at hc
        exact Or.inl hc
      · rw [hc0] at hc
        exact Or.inr hc
    · have hmemg : gateAt C j ∈ C.gates := by
        unfold gateAt
        rw [List.getD_eq_getElem _ _ hjl]
        exact List.getElem_mem _
      have hlen := hAO.2.2 _ hmemg
      have hlt : c < (gateAt C j).inputs.length := by omega
      have hxm : x ∈ (gateAt C j).inputs := by
        rw [← hc, List.getD_eq_getElem _ _ hlt]
        exact List.getElem_mem _
      exact hAO.2.1 j hjl x hxm


end P2487

theorem s2487 : ∀ (n N : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (Pl : Finset (Fin N)) (src top : Fin N → ℕ) (seg : Fin N → ℕ → Prop) (D : ℕ → Finset (Fin N)), PEqualNP.TopForm.IsAO2 n C → (∀ p ∈ Pl, seg p (src p) ∧ seg p (top p) ∧ ∃ j, src p = n + j ∧ j < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and) → (∀ p2 ∈ Pl, ∀ x : ℕ, seg p2 x → p2 ∈ D x ∧ n ≤ x ∧ x < n + C.gates.length) → (∀ p3 ∈ Pl, ∀ x2 : ℕ, seg p3 x2 → x2 ≠ top p3 → ∃ j2 c, j2 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j2).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j2).inputs.getD c 0 = x2 ∧ c < 2 ∧ seg p3 (n + j2) ∧ D x2 ⊆ D (n + j2)) → (∀ g : ℕ, (Pl.filter (fun p4 => src p4 = g)).card ≤ 2) → Pl.card ≤ {x3 : ℕ | ∃ p5 ∈ Pl, seg p5 x3 ∧ 2 ≤ (D x3).card}.ncard + (Pl.image top).card := by
  intro n N C Pl src top seg D hAO h1 h2 h3 h4
  exact PEqualNP.Outside.L_meta_2489.P2487.main n N C Pl src top seg D hAO h1 h2 h3 h4

end Sec2487

theorem len_le2 (n : ℕ) (C : Circuit) (hC : IsAO2 n C) (j : ℕ) :
    (gateAt C j).inputs.length ≤ 2 := by
  by_cases hj : j < C.gates.length
  · exact le_of_eq (hC.2.2 _ (gate_mem C hj))
  · unfold gateAt
    rw [List.getD_eq_default _ _ (by omega)]
    simp

theorem img_le {α β γ : Type} [DecidableEq β] [DecidableEq γ] (A : Finset α) (f : α → β)
    (g : α → γ) (h : ∀ a ∈ A, ∀ b ∈ A, g a = g b → f a = f b) :
    (A.image f).card ≤ (A.image g).card := by
  have e1 : A.image f = (A.image (fun a => (g a, f a))).image Prod.snd := by
    rw [Finset.image_image]
    rfl
  have e2 : A.image g = (A.image (fun a => (g a, f a))).image Prod.fst := by
    rw [Finset.image_image]
    rfl
  have e3 : ((A.image (fun a => (g a, f a))).image Prod.fst).card
      = (A.image (fun a => (g a, f a))).card := by
    apply Finset.card_image_of_injOn
    intro x hx y hy hxy
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hx)
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hy)
    exact Prod.ext hxy (h a ha b hb hxy)
  rw [e1, e2, e3]
  exact Finset.card_image_le

noncomputable def Dd (n N M : ℕ) (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop)
    (C : Circuit) (x : ℕ) : Finset (Fin N) :=
  @Finset.filter (Fin N) (fun p => ∃ m : Fin M, ¬ I p m ∧
    wireVal n C x (fun k : Fin n => decide (k.val ∈ ({pw p, lw m} : Finset ℕ))) = true)
    (Classical.decPred _) Finset.univ

theorem mem_Dd (n N M : ℕ) (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop)
    (C : Circuit) (x : ℕ) (p : Fin N) : p ∈ Dd n N M pw lw I C x ↔ ∃ m : Fin M, ¬ I p m ∧
      wireVal n C x (fun k : Fin n => decide (k.val ∈ ({pw p, lw m} : Finset ℕ))) = true := by
  unfold Dd
  rw [mem_filter']
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

noncomputable def Wd (n N M : ℕ) (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop)
    (C : Circuit) (l : Fin M) : Finset ℕ :=
  @Finset.filter ℕ (fun x => 2 ≤ (Dd n N M pw lw I C x).card ∧ ∀ q ∈ Dd n N M pw lw I C x, I q l)
    (Classical.decPred _) (Finset.Ico n (n + C.gates.length))

theorem mem_Wd (n N M : ℕ) (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop)
    (C : Circuit) (l : Fin M) (x : ℕ) : x ∈ Wd n N M pw lw I C l ↔
      (n ≤ x ∧ x < n + C.gates.length) ∧ 2 ≤ (Dd n N M pw lw I C x).card ∧
        ∀ q ∈ Dd n N M pw lw I C x, I q l := by
  unfold Wd
  rw [mem_filter', Finset.mem_Ico]

theorem perline (n N M : ℕ) (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop)
    (C : Circuit) (hC : IsAO2 n C)
    (hS : ∀ (P_1 : Finset (Fin N)) (Y_1 : Finset (Fin M)), P_1.card ≤ 1 → Y_1.card ≤ 2 →
      (∀ p_3 ∈ P_1, ∀ l_3 ∈ Y_1, ¬ I p_3 l_3) →
      circuitFun n C (fun k_1 : Fin n => decide (k_1.val ∈ P_1.image pw ∪ Y_1.image lw)) = false)
    (l : Fin M) (Pl : Finset (Fin N)) (j1 K F1 V j2 F2 : Fin N → ℕ)
    (h : ∀ p ∈ Pl,
      (j1 p < C.gates.length ∧ (gateAt C (j1 p)).op = GateOp.and ∧
        ((gateAt C (j1 p)).inputs = [K p, F1 p] ∨ (gateAt C (j1 p)).inputs = [F1 p, K p])) ∧
      {a : Fin N | wireVal n C (K p) (fun k : Fin n => decide (k.val = pw a)) = true} = {p} ∧
      (∃ m : Fin M, wireVal n C (F1 p) (fun k : Fin n => decide (k.val = lw m)) = true ∧ ¬ I p m) ∧
      OrReaches n C (V p) (j1 p) ∧
      (j2 p < C.gates.length ∧ (gateAt C (j2 p)).op = GateOp.and ∧
        ((gateAt C (j2 p)).inputs = [V p, F2 p] ∨ (gateAt C (j2 p)).inputs = [F2 p, V p])) ∧
      wireVal n C (F2 p) (fun k : Fin n => decide (k.val = lw l)) = true ∧
      OrReaches n C C.output (j2 p)) :
    Pl.card ≤ (Wd n N M pw lw I C l).card + (Pl.image V).card := by
  refine le_trans (s2487 n N C Pl (fun p => n + j1 p) V
    (fun p x => ∃ j', x = n + j' ∧ j' < C.gates.length ∧ OrReaches n C x (j1 p) ∧
      OrReaches n C (V p) j') (Dd n N M pw lw I C) hC ?_ ?_ ?_ ?_) (Nat.add_le_add_right ?_ _)
  · intro p hp
    obtain ⟨hand1, hK, ⟨m, hm, hnI⟩, hr, hand2, hl, hout⟩ := h p hp
    have hV : n ≤ V p := hr.1
    obtain ⟨k, hk⟩ : ∃ k, V p = n + k := ⟨V p - n, by omega⟩
    have hr2 := hr
    rw [hk] at hr2
    have hklen := ((orReaches_iff n C k (j1 p)).1 hr2).1
    have hself : OrReaches n C (V p) k := by
      rw [hk]
      exact (orReaches_iff n C k k).2 ⟨hklen, Or.inl rfl⟩
    exact ⟨⟨j1 p, rfl, hand1.1, (orReaches_iff n C (j1 p) (j1 p)).2 ⟨hand1.1, Or.inl rfl⟩, hr⟩,
      ⟨k, hk, hklen, hr, hself⟩, j1 p, rfl, hand1.1, hand1.2.1⟩
  · intro p hp x hx
    obtain ⟨j', rfl, hj', hr1, hr2⟩ := hx
    refine ⟨?_, by omega, by omega⟩
    obtain ⟨hand1, hK, ⟨m, hm, hnI⟩, hr, hand2, hl, hout⟩ := h p hp
    rw [mem_Dd]
    refine ⟨m, hnI, ?_⟩
    rw [wires_eq]
    refine reach_up n C _ (j1 p) (n + j') hr1 ?_
    have hKp : wireVal n C (K p) (fun k : Fin n => decide (k.val = pw p)) = true := by
      have hmem : p ∈ {a : Fin N | wireVal n C (K p) (fun k : Fin n => decide (k.val = pw a)) = true} := by
        rw [hK]
        exact Set.mem_singleton p
      exact hmem
    have a1 : val C.gates (K p) (fun k : Fin n => decide (k.val ∈ ({pw p, lw m} : Finset ℕ))) = true := by
      refine wires_mono C hC.1 (fun k : Fin n => decide (k.val = pw p))
        (fun k : Fin n => decide (k.val ∈ ({pw p, lw m} : Finset ℕ))) ?_ (K p) hKp
      intro k hk
      have hk2 := of_decide_eq_true hk
      apply decide_eq_true
      rw [hk2]
      exact Finset.mem_insert_self _ _
    have a2 : val C.gates (F1 p) (fun k : Fin n => decide (k.val ∈ ({pw p, lw m} : Finset ℕ))) = true := by
      refine wires_mono C hC.1 (fun k : Fin n => decide (k.val = lw m))
        (fun k : Fin n => decide (k.val ∈ ({pw p, lw m} : Finset ℕ))) ?_ (F1 p) hm
      intro k hk
      have hk2 := of_decide_eq_true hk
      apply decide_eq_true
      rw [hk2]
      exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    rw [and_eq n C hC _ (j1 p) hand1.1 hand1.2.1]
    rcases hand1.2.2 with e | e
    · rw [e]
      simp only [List.getD_cons_zero, List.getD_cons_succ]
      rw [Bool.and_eq_true]
      exact ⟨a1, a2⟩
    · rw [e]
      simp only [List.getD_cons_zero, List.getD_cons_succ]
      rw [Bool.and_eq_true]
      exact ⟨a2, a1⟩
  · intro p hp x hx hne
    obtain ⟨j', rfl, hj', hr1, hr2⟩ := hx
    obtain ⟨k, c, hk, hop, hmem, hQ, hnQ, hrk⟩ :=
      walk n C hC.2.2 (fun w => w = n + j') j' (V p) hr2 rfl (fun e => hne e.symm)
    have hQ2 : (gateAt C k).inputs.getD (cond c 1 0) 0 = n + j' := hQ
    rw [hQ2] at hmem
    have hlt : n + j' < n + k := hC.2.1 k hk (n + j') hmem
    refine ⟨k, cond c 1 0, hk, hop, hQ2, by cases c <;> simp, ⟨k, rfl, hk, ?_, hrk⟩, ?_⟩
    · exact (orReaches_iff n C k (j1 p)).2 ⟨hk, Or.inr ⟨hop, n + j', hmem, hlt, hr1⟩⟩
    · intro q hq
      rw [mem_Dd] at hq ⊢
      obtain ⟨m, hnI, hw⟩ := hq
      refine ⟨m, hnI, ?_⟩
      rw [wires_eq] at hw ⊢
      exact reach_up n C _ j' (n + k) ((orReaches_iff n C k j').2 ⟨hk, Or.inr ⟨hop, n + j', hmem, hlt,
        (orReaches_iff n C j' j').2 ⟨hj', Or.inl rfl⟩⟩⟩) hw
  · intro g
    refine le_trans (Finset.card_le_card_of_injOn (t := (gateAt C (g - n)).inputs.toFinset) K ?_ ?_)
      (le_trans (List.toFinset_card_le _) (len_le2 n C hC (g - n)))
    · intro p hp
      have hp2 := Finset.mem_filter.1 hp
      obtain ⟨hand1, _⟩ := h p hp2.1
      have e : g - n = j1 p := by
        have := hp2.2
        omega
      refine Finset.mem_coe.2 (List.mem_toFinset.2 ?_)
      rw [e]
      rcases hand1.2.2 with e2 | e2 <;> rw [e2] <;> simp
    · intro p hp q hq hpq
      have hp2 := Finset.mem_filter.1 hp
      have hq2 := Finset.mem_filter.1 hq
      obtain ⟨_, hKp, _⟩ := h p hp2.1
      obtain ⟨_, hKq, _⟩ := h q hq2.1
      rw [hpq] at hKp
      exact Set.singleton_injective (hKp.symm.trans hKq)
  · refine le_trans (Set.ncard_le_ncard (t := ((Wd n N M pw lw I C l : Finset ℕ) : Set ℕ)) ?_
      (Finset.finite_toSet _)) (le_of_eq (Set.ncard_coe_finset _))
    rintro x ⟨p, hp, ⟨j', rfl, hj', hr1, hr2⟩, h2⟩
    rw [Finset.mem_coe, mem_Wd]
    refine ⟨⟨by omega, by omega⟩, h2, ?_⟩
    intro q hq
    obtain ⟨m, hnI, hw⟩ := (mem_Dd n N M pw lw I C (n + j') q).1 hq
    obtain ⟨_, _, _, _, hand, hl, hout⟩ := h p hp
    exact dirty_on n N M pw lw I C l (n + j') (V p) (F2 p) (j2 p) hC hS
      (Or.inr ⟨j', rfl, hr2⟩) hand.1 hand.2.1 hand.2.2 hout hl q m hnI hw

theorem main89 : ∀ (n N M : ℕ) (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop) (C : PEqualNP.CircuitLowerBounds.Circuit) (A : Finset (Fin N × Fin M)), PEqualNP.TopForm.IsAO2 n C → (Function.Injective pw ∧ Function.Injective lw ∧ (∀ p_1 l_1, pw p_1 ≠ lw l_1) ∧ (∀ p_2, pw p_2 < n) ∧ (∀ l_2, lw l_2 < n)) → (∀ p_3 p_4 l_3 l_4, p_3 ≠ p_4 → l_3 ≠ l_4 → ¬ (I p_3 l_3 ∧ I p_4 l_3 ∧ I p_3 l_4 ∧ I p_4 l_4)) → (∀ (P_1 : Finset (Fin N)) (Y_1 : Finset (Fin M)), P_1.card ≤ 1 → Y_1.card ≤ 2 → (∀ p_5 ∈ P_1, ∀ l_5 ∈ Y_1, ¬ I p_5 l_5) → PEqualNP.MetaComplexity.circuitFun n C (fun k_1 : Fin n => decide (k_1.val ∈ P_1.image pw ∪ Y_1.image lw)) = false) → (∀ pl ∈ A, I pl.1 pl.2 ∧ (∃ j_1 K_1 F_1 V_1 j_2 F_2 m_1, (j_1 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_1).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j_1).inputs = [K_1, F_1] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_1).inputs = [F_1, K_1])) ∧ {a_1 | PEqualNP.CleanedNonEdge.wireVal n C (K_1) (fun k_2 : Fin n => decide (k_2.val = pw a_1)) = true} = {pl.1} ∧ m_1 ∈ {a_2 | PEqualNP.CleanedNonEdge.wireVal n C (F_1) (fun k_3 : Fin n => decide (k_3.val = lw a_2)) = true} ∧ ¬ I pl.1 m_1 ∧ PEqualNP.CleanedNonEdge.OrReaches n C (V_1) j_1 ∧ (j_2 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_2).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j_2).inputs = [V_1, F_2] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_2).inputs = [F_2, V_1])) ∧ {a_3 | PEqualNP.CleanedNonEdge.wireVal n C (F_2) (fun k_4 : Fin n => decide (k_4.val = lw a_3)) = true} = {pl.2} ∧ PEqualNP.CleanedNonEdge.OrReaches n C (C.output) j_2)) → A.card ≤ C.size + 2 * {j_3 : ℕ | j_3 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_3).op = PEqualNP.CircuitLowerBounds.GateOp.and}.ncard := by
  intro n N M pw lw I C A hC hinj hno hS hA
  classical
  rcases A.eq_empty_or_nonempty with hAe | ⟨pl0, hpl0⟩
  · rw [hAe]
    simp
  have : Nonempty (Fin M) := ⟨pl0.2⟩
  have hA2 := fun pl (hpl : pl ∈ A) => (hA pl hpl).2
  choose! j1 K F1 V j2 F2 m hch using hA2
  have hper : ∀ l : Fin M, (A.filter (fun pl => pl.2 = l)).card ≤
      (Wd n N M pw lw I C l).card +
        ((Finset.univ.filter (fun p : Fin N => (p, l) ∈ A)).image (fun p => V (p, l))).card := by
    intro l
    have h1 : (A.filter (fun pl => pl.2 = l)).card ≤
        (Finset.univ.filter (fun p : Fin N => (p, l) ∈ A)).card := by
      refine Finset.card_le_card_of_injOn Prod.fst ?_ ?_
      · intro pl hpl
        have h2 := Finset.mem_filter.1 hpl
        refine Finset.mem_coe.2 (Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩)
        have e : (pl.1, l) = pl := Prod.ext rfl h2.2.symm
        rw [e]
        exact h2.1
      · intro a ha b hb hab
        have h2 := Finset.mem_filter.1 ha
        have h3 := Finset.mem_filter.1 hb
        exact Prod.ext hab (h2.2.trans h3.2.symm)
    refine le_trans h1 (perline n N M pw lw I C hC hS l _ (fun p => j1 (p, l)) (fun p => K (p, l))
      (fun p => F1 (p, l)) (fun p => V (p, l)) (fun p => j2 (p, l)) (fun p => F2 (p, l)) ?_)
    intro p hp
    have hpA : (p, l) ∈ A := (Finset.mem_filter.1 hp).2
    obtain ⟨a, b, c, d, e, f, g, hh⟩ := hch (p, l) hpA
    have hl : l ∈ {a_3 : Fin M | wireVal n C (F2 (p, l)) (fun k : Fin n => decide (k.val = lw a_3)) = true} := by
      rw [g]
      exact Set.mem_singleton l
    exact ⟨a, b, ⟨m (p, l), c, d⟩, e, f, hl, hh⟩
  have hsum : A.card = ∑ l : Fin M, (A.filter (fun pl => pl.2 = l)).card :=
    Finset.card_eq_sum_card_fiberwise (f := Prod.snd) (fun _ _ => Finset.mem_univ _)
  have hW : ∑ l : Fin M, (Wd n N M pw lw I C l).card ≤ C.gates.length := by
    have hd : ∀ l ∈ (Finset.univ : Finset (Fin M)), ∀ l' ∈ (Finset.univ : Finset (Fin M)), l ≠ l' →
        Disjoint (Wd n N M pw lw I C l) (Wd n N M pw lw I C l') := by
      intro l _ l' _ hll
      rw [Finset.disjoint_left]
      intro x hx hx'
      rw [mem_Wd] at hx hx'
      obtain ⟨q1, hq1, q2, hq2, hne⟩ := Finset.one_lt_card.1 hx.2.1
      exact hno q1 q2 l l' hne hll ⟨hx.2.2 q1 hq1, hx.2.2 q2 hq2, hx'.2.2 q1 hq1, hx'.2.2 q2 hq2⟩
    rw [← Finset.card_biUnion hd]
    refine le_trans (Finset.card_le_card (t := Finset.Ico n (n + C.gates.length))
      (Finset.biUnion_subset.2 (fun l _ x hx =>
        Finset.mem_Ico.2 ((mem_Wd n N M pw lw I C l x).1 hx).1))) ?_
    simp
  have hfin : {j : ℕ | j < C.gates.length ∧ (gateAt C j).op = GateOp.and}.Finite :=
    (Set.finite_lt_nat C.gates.length).subset (fun x hx => hx.1)
  have hT : ∑ l : Fin M,
      ((Finset.univ.filter (fun p : Fin N => (p, l) ∈ A)).image (fun p => V (p, l))).card
      ≤ 2 * {j : ℕ | j < C.gates.length ∧ (gateAt C j).op = GateOp.and}.ncard := by
    have s1 : ∀ l : Fin M,
        ((Finset.univ.filter (fun p : Fin N => (p, l) ∈ A)).image (fun p => V (p, l))).card
        ≤ ((A.image (fun pl => (pl.2, V pl))).filter (fun t => t.1 = l)).card := by
      intro l
      refine Finset.card_le_card_of_injOn (fun v => (l, v)) ?_ ?_
      · intro v hv
        obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hv
        exact Finset.mem_coe.2 (Finset.mem_filter.2
          ⟨Finset.mem_image.2 ⟨(p, l), (Finset.mem_filter.1 hp).2, rfl⟩, rfl⟩)
      · intro a _ b _ hab
        exact (Prod.mk.inj hab).2
    have s2 : (A.image (fun pl => (pl.2, V pl))).card
        = ∑ l : Fin M, ((A.image (fun pl => (pl.2, V pl))).filter (fun t => t.1 = l)).card :=
      Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (fun _ _ => Finset.mem_univ _)
    have s3 : (A.image (fun pl => (pl.2, V pl))).card ≤ (A.image (fun pl => (j2 pl, V pl))).card := by
      refine img_le A _ _ ?_
      intro a ha b hb hab
      have hj : j2 a = j2 b := (Prod.mk.inj hab).1
      have hv : V a = V b := (Prod.mk.inj hab).2
      obtain ⟨_, _, _, _, _, fa, ga, _⟩ := hch a ha
      obtain ⟨_, _, _, _, _, fb, gb, _⟩ := hch b hb
      have hF : F2 a = F2 b := by
        have ia := fa.2.2
        have ib := fb.2.2
        rw [← hj, ← hv] at ib
        rcases ia with ia | ia <;> rcases ib with ib | ib <;> rw [ia] at ib <;> simp at ib <;> omega
      rw [← hF] at gb
      have hl : a.2 = b.2 := Set.singleton_injective (ga.symm.trans gb)
      exact Prod.ext hl hv
    have s4 : (A.image (fun pl => (j2 pl, V pl))).card ≤ 2 * hfin.toFinset.card := by
      have hsub : A.image (fun pl => (j2 pl, V pl)) ⊆
          hfin.toFinset.biUnion (fun j => ((gateAt C j).inputs.toFinset).image (fun v => (j, v))) := by
        intro t ht
        obtain ⟨pl, hpl, rfl⟩ := Finset.mem_image.1 ht
        obtain ⟨_, _, _, _, _, f, _, _⟩ := hch pl hpl
        refine Finset.mem_biUnion.2 ⟨j2 pl, hfin.mem_toFinset.2 ⟨f.1, f.2.1⟩,
          Finset.mem_image.2 ⟨V pl, ?_, rfl⟩⟩
        rw [List.mem_toFinset]
        rcases f.2.2 with e | e <;> rw [e] <;> simp
      refine le_trans (Finset.card_le_card hsub) (le_trans Finset.card_biUnion_le ?_)
      refine le_trans (Finset.sum_le_card_nsmul _ _ 2 ?_) (le_of_eq ?_)
      · intro j _
        exact le_trans Finset.card_image_le
          (le_trans (List.toFinset_card_le _) (len_le2 n C hC j))
      · rw [smul_eq_mul, Nat.mul_comm]
    rw [Set.ncard_eq_toFinset_card _ hfin]
    exact le_trans (Finset.sum_le_sum (fun l _ => s1 l))
      (le_trans (le_of_eq s2.symm) (le_trans s3 s4))
  have hsz : C.size = C.gates.length := rfl
  rw [hsz, hsum]
  refine le_trans (Finset.sum_le_sum (fun l _ => hper l)) ?_
  rw [Finset.sum_add_distrib]
  exact Nat.add_le_add hW hT

end PEqualNP.Outside.L_meta_2489

theorem PEqualNP.Outside.L_meta_2489 : ∀ (n N M : ℕ) (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop) (C : PEqualNP.CircuitLowerBounds.Circuit) (A : Finset (Fin N × Fin M)), PEqualNP.TopForm.IsAO2 n C → (Function.Injective pw ∧ Function.Injective lw ∧ (∀ p_1 l_1, pw p_1 ≠ lw l_1) ∧ (∀ p_2, pw p_2 < n) ∧ (∀ l_2, lw l_2 < n)) → (∀ p_3 p_4 l_3 l_4, p_3 ≠ p_4 → l_3 ≠ l_4 → ¬ (I p_3 l_3 ∧ I p_4 l_3 ∧ I p_3 l_4 ∧ I p_4 l_4)) → (∀ (P_1 : Finset (Fin N)) (Y_1 : Finset (Fin M)), P_1.card ≤ 1 → Y_1.card ≤ 2 → (∀ p_5 ∈ P_1, ∀ l_5 ∈ Y_1, ¬ I p_5 l_5) → PEqualNP.MetaComplexity.circuitFun n C (fun k_1 : Fin n => decide (k_1.val ∈ P_1.image pw ∪ Y_1.image lw)) = false) → (∀ pl ∈ A, I pl.1 pl.2 ∧ (∃ j_1 K_1 F_1 V_1 j_2 F_2 m_1, (j_1 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_1).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j_1).inputs = [K_1, F_1] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_1).inputs = [F_1, K_1])) ∧ {a_1 | PEqualNP.CleanedNonEdge.wireVal n C (K_1) (fun k_2 : Fin n => decide (k_2.val = pw a_1)) = true} = {pl.1} ∧ m_1 ∈ {a_2 | PEqualNP.CleanedNonEdge.wireVal n C (F_1) (fun k_3 : Fin n => decide (k_3.val = lw a_2)) = true} ∧ ¬ I pl.1 m_1 ∧ PEqualNP.CleanedNonEdge.OrReaches n C (V_1) j_1 ∧ (j_2 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_2).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j_2).inputs = [V_1, F_2] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_2).inputs = [F_2, V_1])) ∧ {a_3 | PEqualNP.CleanedNonEdge.wireVal n C (F_2) (fun k_4 : Fin n => decide (k_4.val = lw a_3)) = true} = {pl.2} ∧ PEqualNP.CleanedNonEdge.OrReaches n C (C.output) j_2)) → A.card ≤ C.size + 2 * {j_3 : ℕ | j_3 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_3).op = PEqualNP.CircuitLowerBounds.GateOp.and}.ncard := by
  exact PEqualNP.Outside.L_meta_2489.main89
