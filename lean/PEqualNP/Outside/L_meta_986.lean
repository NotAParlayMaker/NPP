import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_986

open PEqualNP.CircuitLowerBounds

private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private def val {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ) : Bool :=
  (gs.foldl step (List.ofFn x)).getD i false

private lemma fold_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, List.length_cons]
    simp only [step, List.length_append, List.length_cons, List.length_nil]
    omega

private lemma val_nil {n : ℕ} (x : Fin n → Bool) (i : ℕ) :
    val [] x i = if h : i < n then x ⟨i, h⟩ else false := by
  unfold val
  by_cases h : i < n
  · simp [List.getD_eq_getElem?_getD, h]
  · simp [List.getD_eq_getElem?_getD, h]

private lemma val_snoc {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) (i : ℕ) :
    val (gs ++ [g]) x i =
      if i = n + gs.length then g.op.eval (g.inputs.map fun j => val gs x j)
      else val gs x i := by
  unfold val
  rw [List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil, step]
  have hl : (gs.foldl step (List.ofFn x)).length = n + gs.length := by
    rw [fold_length]
    simp
  rcases lt_trichotomy i (n + gs.length) with h | h | h
  · rw [ite_eq_right (by omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left (by omega)]
  · rw [ite_eq_left h]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by omega)]
    simp [hl, h]
  · rw [ite_eq_right (by omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

private lemma val_append_lt {n : ℕ} (gs1 gs2 : List Gate) (x : Fin n → Bool) {i : ℕ}
    (hi : i < n + gs1.length) : val (gs1 ++ gs2) x i = val gs1 x i := by
  induction gs2 using List.reverseRecOn with
  | nil => simp
  | append_singleton gs2 g ih =>
    rw [← List.append_assoc, val_snoc, ite_eq_right (by simp; omega)]
    exact ih

private lemma gate_cases {X : Type} (g : Gate) (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    (hlen : g.inputs.length ≤ 2) (f : X → ℕ → Bool) (z : X) :
    (∀ y, g.op.eval (g.inputs.map (f y)) = false) ∨
    ∃ a b, g.op.eval (g.inputs.map (f z)) = false →
      (f z a = false ∧ f z b = false ∧
        ∀ y, g.op.eval (g.inputs.map (f y)) = true → f y a = true ∨ f y b = true) := by
  obtain ⟨op, ins⟩ := g
  simp only at hop hlen ⊢
  match ins, hlen with
  | [], _ =>
    rcases hop with rfl | rfl
    · right
      exact ⟨0, 0, by simp [GateOp.eval]⟩
    · left
      simp [GateOp.eval]
  | [a], _ =>
    right
    refine ⟨a, a, ?_⟩
    rcases hop with rfl | rfl <;> simp [GateOp.eval]
  | [a, b], _ =>
    rcases hop with rfl | rfl
    · right
      by_cases h : f z a = false
      · refine ⟨a, a, ?_⟩
        simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
          Bool.and_true, id_eq, Bool.and_eq_true]
        intro _
        exact ⟨h, h, fun y hy => Or.inl hy.1⟩
      · refine ⟨b, b, ?_⟩
        simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
          Bool.and_true, id_eq, Bool.and_eq_true]
        intro hz
        have hb : f z b = false := by
          cases ha : f z a <;> cases hb : f z b <;> simp_all
        exact ⟨hb, hb, fun y hy => Or.inl hy.2⟩
    · right
      refine ⟨a, b, ?_⟩
      simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
        Bool.or_false, id_eq, Bool.or_eq_true, Bool.or_eq_false_iff]
      intro hz
      exact ⟨hz.1, hz.2, fun y hy => hy⟩
  | _ :: _ :: _ :: _, h => simp at h

private def Zof {n : ℕ} (S T : Finset (Fin n)) : Fin n → Bool :=
  fun c => decide (c ∉ S ∧ c ∉ T)

private def eof {n : ℕ} (u : Fin n) : Fin n → Bool :=
  fun c => decide (c = u)

private def Inv {n : ℕ} (A U S T : Finset (Fin n)) (gs : List Gate) (l : Fin n → Fin n) : Prop :=
  ∀ i u v, u ∈ U → v ∈ U → val gs (Zof S T) i = false →
    val gs (eof u) i = true → val gs (eof v) i = true →
    u ∈ A ∧ l u = l v

private def Cnt {n : ℕ} (U S T : Finset (Fin n)) (gs : List Gate) (i : ℕ) : Prop :=
  val gs (Zof S T) i = false ∧
    ∃ u v : Fin n, u ∈ U ∧ v ∈ U ∧ u ≠ v ∧ val gs (eof u) i = true ∧ val gs (eof v) i = true

open Classical in
private noncomputable def D {n : ℕ} (U S T : Finset (Fin n)) (gs : List Gate) : Finset ℕ :=
  (Finset.Ico n (n + gs.length)).filter fun i => Cnt U S T gs i

private lemma D_mono {n : ℕ} (U S T : Finset (Fin n)) (gs : List Gate) (g : Gate) :
    D U S T gs ⊆ D U S T (gs ++ [g]) := by
  classical
  intro i hi
  simp only [D, Finset.mem_filter, Finset.mem_Ico, List.length_append, List.length_cons,
    List.length_nil] at hi ⊢
  refine ⟨⟨hi.1.1, by omega⟩, ?_⟩
  have hne : i ≠ n + gs.length := by omega
  obtain ⟨hz, u, v, huU, hvU, huv, hu, hv⟩ := hi.2
  refine ⟨?_, u, v, huU, hvU, huv, ?_, ?_⟩
  · rw [val_snoc, ite_eq_right hne]; exact hz
  · rw [val_snoc, ite_eq_right hne]; exact hu
  · rw [val_snoc, ite_eq_right hne]; exact hv

private lemma main_inv {n : ℕ} (A U S T : Finset (Fin n)) (gates : List Gate)
    (hbase : ∀ u ∈ U, (u ∈ S ∨ u ∈ T) → u ∈ A)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (hnot_true : ∀ (k : ℕ) (hk : k < gates.length),
      (gates[k]).op = GateOp.not → val (gates.take (k + 1)) (Zof S T) (n + k) = true) :
    ∀ k ≤ gates.length,
      ∃ l : Fin n → Fin n, Inv A U S T (gates.take k) l ∧
        A.card ≤ (A.image l).card + (D U S T (gates.take k)).card := by
  classical
  intro k hk
  induction k with
  | zero =>
    refine ⟨id, ?_, by simp⟩
    intro i u v huU hvU hz hu hv
    rw [List.take_zero, val_nil] at hz hu hv
    by_cases h : i < n
    · simp only [h, dite_true, Zof, eof, decide_eq_false_iff_not, not_and_or, not_not,
        decide_eq_true_eq] at hz hu hv
      have hu_eq : u = ⟨i, h⟩ := hu.symm
      have hv_eq : v = ⟨i, h⟩ := hv.symm
      rw [← hu_eq] at hz
      exact ⟨hbase u huU hz, by rw [hu_eq, hv_eq]⟩
    · simp [h] at hu
  | succ k ih =>
    obtain ⟨l, hinv, hcard⟩ := ih (Nat.le_of_succ_le hk)
    have hkl : k < gates.length := hk
    set gs := gates.take k with hgs
    set g := gates[k] with hg_def
    have htake : gates.take (k + 1) = gs ++ [g] := List.take_succ_eq_append_getElem hkl
    have hgslen : gs.length = k := List.length_take_of_le (Nat.le_of_succ_le hk)
    obtain ⟨hop, hlen⟩ := hg g (List.getElem_mem hkl)
    set N := n + gs.length with hN
    set P : (Fin n → Bool) → Bool := fun x => g.op.eval (g.inputs.map fun j => val gs x j) with hP
    have hnew : ∀ x : Fin n → Bool, val (gs ++ [g]) x N = P x := by
      intro x; rw [val_snoc, ite_eq_left hN]
    have hold : ∀ (x : Fin n → Bool) (i : ℕ), i ≠ N → val (gs ++ [g]) x i = val gs x i := by
      intro x i hi; rw [val_snoc, ite_eq_right hi]
    rw [htake]
    rcases hop with hop | hop | hop
    · have hmono : g.op = GateOp.and ∨ g.op = GateOp.or := Or.inl hop
      have key : P (Zof S T) = false → ∀ u ∈ U, P (eof u) = true →
          u ∈ A ∧ ∃ B1 B2 : Fin n → Prop, (∀ w ∈ U, P (eof w) = true → B1 w ∨ B2 w) ∧
            (∀ w ∈ U, ∀ w' ∈ U, B1 w → B1 w' → l w = l w') ∧
            (∀ w ∈ U, ∀ w' ∈ U, B2 w → B2 w' → l w = l w') := by
        intro hz u huU hu
        rcases gate_cases g hmono hlen (fun x j => val gs x j) (Zof S T) with hall | ⟨a, b, hab⟩
        · have := hall (eof u)
          simp only [hP] at hu
          rw [this] at hu
          exact absurd hu (by simp)
        · obtain ⟨ha, hb, hy⟩ := hab hz
          refine ⟨?_, fun w => val gs (eof w) a = true, fun w => val gs (eof w) b = true,
            fun w _ hw => hy (eof w) hw,
            fun w hwU w' hw'U hw hw' => (hinv a w w' hwU hw'U ha hw hw').2,
            fun w hwU w' hw'U hw hw' => (hinv b w w' hwU hw'U hb hw hw').2⟩
          rcases hy (eof u) hu with h | h
          · exact (hinv a u u huU huU ha h h).1
          · exact (hinv b u u huU huU hb h h).1
      by_cases hm : P (Zof S T) = false ∧ ∃ u v, u ∈ U ∧ v ∈ U ∧ P (eof u) = true ∧ P (eof v) = true ∧ l u ≠ l v
      · obtain ⟨hz, u0, v0, hu0U, hv0U, hu0, hv0, hne⟩ := hm
        refine ⟨fun w => if l w = l v0 then l u0 else l w, ?_, ?_⟩
        · intro i u v huU hvU hiz hiu hiv
          by_cases hi : i = N
          · subst hi
            rw [hnew] at hiz hiu hiv
            obtain ⟨huA, B1, B2, hAB, hB1, hB2⟩ := key hiz u huU hiu
            refine ⟨huA, ?_⟩
            have two : ∀ w ∈ U, P (eof w) = true → l w = l u0 ∨ l w = l v0 := by
              intro w hwU hw
              rcases hAB w hwU hw with h | h <;> rcases hAB u0 hu0U hu0 with h0 | h0 <;>
                rcases hAB v0 hv0U hv0 with h1 | h1
              · exact Or.inl (hB1 w hwU u0 hu0U h h0)
              · exact Or.inl (hB1 w hwU u0 hu0U h h0)
              · exact Or.inr (hB1 w hwU v0 hv0U h h1)
              · exact absurd (hB2 u0 hu0U v0 hv0U h0 h1) hne
              · exact absurd (hB1 u0 hu0U v0 hv0U h0 h1) hne
              · exact Or.inr (hB2 w hwU v0 hv0U h h1)
              · exact Or.inl (hB2 w hwU u0 hu0U h h0)
              · exact Or.inl (hB2 w hwU u0 hu0U h h0)
            have red : ∀ w ∈ U, P (eof w) = true → (if l w = l v0 then l u0 else l w) = l u0 := by
              intro w hwU hw
              rcases two w hwU hw with h | h
              · rw [h]; split_ifs <;> rfl
              · rw [ite_eq_left h]
            show (if l u = l v0 then l u0 else l u) = (if l v = l v0 then l u0 else l v)
            rw [red u huU hiu, red v hvU hiv]
          · rw [hold _ _ hi] at hiz hiu hiv
            obtain ⟨huA, hl⟩ := hinv i u v huU hvU hiz hiu hiv
            refine ⟨huA, ?_⟩
            show (if l u = l v0 then l u0 else l u) = (if l v = l v0 then l u0 else l v)
            rw [hl]
        · have himg : A.image l ⊆
              insert (l v0) (A.image fun w => if l w = l v0 then l u0 else l w) := by
            intro y hy
            obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hy
            by_cases h : l w = l v0
            · rw [h]; exact Finset.mem_insert_self _ _
            · refine Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨w, hw, ?_⟩)
              rw [ite_eq_right h]
          have h1 : (A.image l).card ≤
              (A.image fun w => if l w = l v0 then l u0 else l w).card + 1 :=
            (Finset.card_le_card himg).trans (Finset.card_insert_le _ _)
          have hNin : N ∈ D U S T (gs ++ [g]) := by
            simp only [D, Finset.mem_filter, Finset.mem_Ico, List.length_append,
              List.length_cons, List.length_nil]
            refine ⟨⟨by omega, by omega⟩, ?_, u0, v0, hu0U, hv0U, ?_, ?_, ?_⟩
            · rw [hnew]; exact hz
            · intro h; exact hne (by rw [h])
            · rw [hnew]; exact hu0
            · rw [hnew]; exact hv0
          have hNnot : N ∉ D U S T gs := by
            simp only [D, Finset.mem_filter, Finset.mem_Ico]
            intro h; omega
          have h2 : (D U S T gs).card + 1 ≤ (D U S T (gs ++ [g])).card := by
            rw [← Finset.card_insert_of_notMem hNnot]
            apply Finset.card_le_card
            intro i hi
            rcases Finset.mem_insert.mp hi with rfl | hi
            · exact hNin
            · exact D_mono U S T gs g hi
          omega
      · refine ⟨l, ?_, ?_⟩
        · intro i u v huU hvU hiz hiu hiv
          by_cases hi : i = N
          · subst hi
            rw [hnew] at hiz hiu hiv
            obtain ⟨huA, -⟩ := key hiz u huU hiu
            refine ⟨huA, ?_⟩
            by_contra hne
            exact hm ⟨hiz, u, v, huU, hvU, hiu, hiv, hne⟩
          · rw [hold _ _ hi] at hiz hiu hiv
            exact hinv i u v huU hvU hiz hiu hiv
        · have := Finset.card_le_card (D_mono U S T gs g)
          omega
    · have hmono : g.op = GateOp.and ∨ g.op = GateOp.or := Or.inr hop
      have key : P (Zof S T) = false → ∀ u ∈ U, P (eof u) = true →
          u ∈ A ∧ ∃ B1 B2 : Fin n → Prop, (∀ w ∈ U, P (eof w) = true → B1 w ∨ B2 w) ∧
            (∀ w ∈ U, ∀ w' ∈ U, B1 w → B1 w' → l w = l w') ∧
            (∀ w ∈ U, ∀ w' ∈ U, B2 w → B2 w' → l w = l w') := by
        intro hz u huU hu
        rcases gate_cases g hmono hlen (fun x j => val gs x j) (Zof S T) with hall | ⟨a, b, hab⟩
        · have := hall (eof u)
          simp only [hP] at hu
          rw [this] at hu
          exact absurd hu (by simp)
        · obtain ⟨ha, hb, hy⟩ := hab hz
          refine ⟨?_, fun w => val gs (eof w) a = true, fun w => val gs (eof w) b = true,
            fun w _ hw => hy (eof w) hw,
            fun w hwU w' hw'U hw hw' => (hinv a w w' hwU hw'U ha hw hw').2,
            fun w hwU w' hw'U hw hw' => (hinv b w w' hwU hw'U hb hw hw').2⟩
          rcases hy (eof u) hu with h | h
          · exact (hinv a u u huU huU ha h h).1
          · exact (hinv b u u huU huU hb h h).1
      by_cases hm : P (Zof S T) = false ∧ ∃ u v, u ∈ U ∧ v ∈ U ∧ P (eof u) = true ∧ P (eof v) = true ∧ l u ≠ l v
      · obtain ⟨hz, u0, v0, hu0U, hv0U, hu0, hv0, hne⟩ := hm
        refine ⟨fun w => if l w = l v0 then l u0 else l w, ?_, ?_⟩
        · intro i u v huU hvU hiz hiu hiv
          by_cases hi : i = N
          · subst hi
            rw [hnew] at hiz hiu hiv
            obtain ⟨huA, B1, B2, hAB, hB1, hB2⟩ := key hiz u huU hiu
            refine ⟨huA, ?_⟩
            have two : ∀ w ∈ U, P (eof w) = true → l w = l u0 ∨ l w = l v0 := by
              intro w hwU hw
              rcases hAB w hwU hw with h | h <;> rcases hAB u0 hu0U hu0 with h0 | h0 <;>
                rcases hAB v0 hv0U hv0 with h1 | h1
              · exact Or.inl (hB1 w hwU u0 hu0U h h0)
              · exact Or.inl (hB1 w hwU u0 hu0U h h0)
              · exact Or.inr (hB1 w hwU v0 hv0U h h1)
              · exact absurd (hB2 u0 hu0U v0 hv0U h0 h1) hne
              · exact absurd (hB1 u0 hu0U v0 hv0U h0 h1) hne
              · exact Or.inr (hB2 w hwU v0 hv0U h h1)
              · exact Or.inl (hB2 w hwU u0 hu0U h h0)
              · exact Or.inl (hB2 w hwU u0 hu0U h h0)
            have red : ∀ w ∈ U, P (eof w) = true → (if l w = l v0 then l u0 else l w) = l u0 := by
              intro w hwU hw
              rcases two w hwU hw with h | h
              · rw [h]; split_ifs <;> rfl
              · rw [ite_eq_left h]
            show (if l u = l v0 then l u0 else l u) = (if l v = l v0 then l u0 else l v)
            rw [red u huU hiu, red v hvU hiv]
          · rw [hold _ _ hi] at hiz hiu hiv
            obtain ⟨huA, hl⟩ := hinv i u v huU hvU hiz hiu hiv
            refine ⟨huA, ?_⟩
            show (if l u = l v0 then l u0 else l u) = (if l v = l v0 then l u0 else l v)
            rw [hl]
        · have himg : A.image l ⊆
              insert (l v0) (A.image fun w => if l w = l v0 then l u0 else l w) := by
            intro y hy
            obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hy
            by_cases h : l w = l v0
            · rw [h]; exact Finset.mem_insert_self _ _
            · refine Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨w, hw, ?_⟩)
              rw [ite_eq_right h]
          have h1 : (A.image l).card ≤
              (A.image fun w => if l w = l v0 then l u0 else l w).card + 1 :=
            (Finset.card_le_card himg).trans (Finset.card_insert_le _ _)
          have hNin : N ∈ D U S T (gs ++ [g]) := by
            simp only [D, Finset.mem_filter, Finset.mem_Ico, List.length_append,
              List.length_cons, List.length_nil]
            refine ⟨⟨by omega, by omega⟩, ?_, u0, v0, hu0U, hv0U, ?_, ?_, ?_⟩
            · rw [hnew]; exact hz
            · intro h; exact hne (by rw [h])
            · rw [hnew]; exact hu0
            · rw [hnew]; exact hv0
          have hNnot : N ∉ D U S T gs := by
            simp only [D, Finset.mem_filter, Finset.mem_Ico]
            intro h; omega
          have h2 : (D U S T gs).card + 1 ≤ (D U S T (gs ++ [g])).card := by
            rw [← Finset.card_insert_of_notMem hNnot]
            apply Finset.card_le_card
            intro i hi
            rcases Finset.mem_insert.mp hi with rfl | hi
            · exact hNin
            · exact D_mono U S T gs g hi
          omega
      · refine ⟨l, ?_, ?_⟩
        · intro i u v huU hvU hiz hiu hiv
          by_cases hi : i = N
          · subst hi
            rw [hnew] at hiz hiu hiv
            obtain ⟨huA, -⟩ := key hiz u huU hiu
            refine ⟨huA, ?_⟩
            by_contra hne
            exact hm ⟨hiz, u, v, huU, hvU, hiu, hiv, hne⟩
          · rw [hold _ _ hi] at hiz hiu hiv
            exact hinv i u v huU hvU hiz hiu hiv
        · have := Finset.card_le_card (D_mono U S T gs g)
          omega
    · have hnt : val (gs ++ [g]) (Zof S T) N = true := by
        have h1 := hnot_true k hkl hop
        rw [htake, ← hgslen] at h1
        exact h1
      refine ⟨l, ?_, ?_⟩
      · intro i u v huU hvU hiz hiu hiv
        by_cases hi : i = N
        · subst hi
          rw [hnt] at hiz
          exact absurd hiz (by decide)
        · rw [hold _ _ hi] at hiz hiu hiv
          exact hinv i u v huU hvU hiz hiu hiv
      · have := Finset.card_le_card (D_mono U S T gs g)
        omega

private lemma main_proof
    (n m : ℕ) (S : Fin m → Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ)
    (i0 : Fin gates.length) (hw : ℕ) (T : Finset (Fin n)) (t0 : Fin n)
    (_hS2 : ∀ i : Fin m, 2 ≤ (S i).card)
    (hSinter : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (hnot_only : ∀ q : Fin gates.length, (gates.get q).op = GateOp.not → q = i0)
    (hnot_at : (gates.get i0).op = GateOp.not)
    (hnot_in : (gates.get i0).inputs.head? = some hw)
    (hhw_lt : hw < n + i0.val)
    (hev : ∀ (o : Fin m) (x : Fin n → Bool), Circuit.eval ⟨gates, out o⟩ (List.ofFn x) = decide (∃ v ∈ S o, x v = true))
    (hT : ∀ y : Fin n → Bool, (∀ t ∈ T, y t = false) → Circuit.eval ⟨gates, hw⟩ (List.ofFn y) = false)
    (_ht0 : t0 ∈ T)
    (_ht0_max : ∀ t ∈ T, (Finset.univ.filter (fun a : Fin m => t ∈ S a)).card ≤ (Finset.univ.filter (fun b : Fin m => t0 ∈ S b)).card) :
    1 + ∑ s : Fin m, ((S s).card - 1) ≤ gates.length + ∑ u ∈ T.erase t0, (Finset.univ.filter (fun c : Fin m => u ∈ S c)).card := by
  classical
  let T' := T.erase t0
  let A : Fin m → Finset (Fin n) := fun w => S w \ T'
  let U : Fin m → Finset (Fin n) := fun w => if t0 ∈ S w then Finset.univ \ T' else Finset.univ \ T
  have hval : ∀ (o : Fin m) (x : Fin n → Bool), val gates x (out o) = decide (∃ v ∈ S o, x v = true) :=
    fun o x => hev o x
  have hnot_true : ∀ (w : Fin m) (k : ℕ) (hk : k < gates.length),
      (gates[k]).op = GateOp.not → val (gates.take (k + 1)) (Zof (S w) T) (n + k) = true := by
    intro w k hk hkop
    have hkeq : (⟨k, hk⟩ : Fin gates.length) = i0 := hnot_only ⟨k, hk⟩ (by simpa using hkop)
    have hkv : k = i0.val := congrArg Fin.val hkeq
    subst hkv
    have htake : gates.take (i0.val + 1) = gates.take i0.val ++ [gates[i0.val]] :=
      List.take_succ_eq_append_getElem i0.isLt
    have hlen_take : (gates.take i0.val).length = i0.val := List.length_take_of_le (le_of_lt i0.isLt)
    rw [htake, val_snoc, hlen_take, ite_eq_left rfl]
    have hget_eq : gates[i0.val] = gates.get i0 := rfl
    rw [hget_eq, hnot_at]
    have hhead : (gates.get i0).inputs.head? = some hw := hnot_in
    cases hins : (gates.get i0).inputs with
    | nil => rw [hins] at hhead; simp at hhead
    | cons a rest =>
      rw [hins] at hhead
      simp only [List.head?_cons, Option.some.injEq] at hhead
      subst a
      simp only [GateOp.eval, List.map_cons, List.headD_cons]
      have hhw_val : val (gates.take i0.val) (Zof (S w) T) hw = val gates (Zof (S w) T) hw := by
        have h := val_append_lt (gates.take i0.val) (gates.drop i0.val) (Zof (S w) T)
          (by rw [hlen_take]; exact hhw_lt)
        rw [List.take_append_drop] at h
        exact h.symm
      rw [hhw_val]
      have hZ_false : ∀ t ∈ T, Zof (S w) T t = false := by
        intro t ht; simp [Zof, ht]
      have hhw0 : val gates (Zof (S w) T) hw = false := hT (Zof (S w) T) hZ_false
      rw [hhw0]; rfl
  have hi0_true : ∀ w : Fin m, val gates (Zof (S w) T) (n + i0.val) = true := by
    intro w
    have hlt : n + i0.val < n + (gates.take (i0.val + 1)).length := by
      rw [List.length_take_of_le (Nat.succ_le_of_lt i0.isLt)]; omega
    have h := val_append_lt (gates.take (i0.val + 1)) (gates.drop (i0.val + 1)) (Zof (S w) T) hlt
    rw [List.take_append_drop] at h
    rw [h]
    exact hnot_true w i0.val i0.isLt (by simpa using hnot_at)
  have hbase : ∀ w : Fin m, ∀ u ∈ U w, (u ∈ S w ∨ u ∈ T) → u ∈ A w := by
    intro w u huU huST
    simp only [A, Finset.mem_sdiff]
    by_cases ht0w : t0 ∈ S w
    · simp only [U, ite_eq_left ht0w, Finset.mem_sdiff, Finset.mem_univ, true_and] at huU
      refine ⟨?_, huU⟩
      rcases huST with h | h
      · exact h
      · by_cases hut0 : u = t0
        · rw [hut0]; exact ht0w
        · exact absurd (Finset.mem_erase.mpr ⟨hut0, h⟩) huU
    · simp only [U, ite_eq_right ht0w, Finset.mem_sdiff, Finset.mem_univ, true_and] at huU
      rcases huST with h | h
      · exact ⟨h, fun h' => huU (Finset.mem_of_mem_erase h')⟩
      · exact absurd h huU
  have hinv_all : ∀ w : Fin m, ∃ l : Fin n → Fin n,
      Inv (A w) (U w) (S w) T gates l ∧ (A w).card ≤ ((A w).image l).card + (D (U w) (S w) T gates).card := by
    intro w
    have h := main_inv (A w) (U w) (S w) T gates (hbase w) hg (hnot_true w) gates.length (le_refl _)
    simpa [List.take_length] using h
  have hbound : ∀ w : Fin m, (A w).card - 1 ≤ (D (U w) (S w) T gates).card := by
    intro w
    obtain ⟨l, hinv, hcard⟩ := hinv_all w
    by_cases hne : (A w).Nonempty
    · obtain ⟨u0, hu0⟩ := hne
      have hAsubU : A w ⊆ U w := by
        intro u hu
        simp only [A, Finset.mem_sdiff] at hu
        by_cases ht0w : t0 ∈ S w
        · simp [U, ht0w, hu.2]
        · simp only [U, ite_eq_right ht0w, Finset.mem_sdiff, Finset.mem_univ, true_and]
          intro huT
          by_cases hut0 : u = t0
          · rw [hut0] at hu; exact ht0w hu.1
          · exact hu.2 (Finset.mem_erase.mpr ⟨hut0, huT⟩)
      have hZout : val gates (Zof (S w) T) (out w) = false := by
        rw [hval]
        simp only [decide_eq_false_iff_not, not_exists, not_and]
        intro v hv
        simp [Zof, hv]
      have hEout : ∀ u ∈ A w, val gates (eof u) (out w) = true := by
        intro u hu
        rw [hval]
        simp only [decide_eq_true_eq]
        exact ⟨u, (Finset.mem_sdiff.mp hu).1, by simp [eof]⟩
      have himg_sub : (A w).image l ⊆ {l u0} := by
        intro y hy
        obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hy
        rw [Finset.mem_singleton]
        exact (hinv (out w) u u0 (hAsubU hu) (hAsubU hu0) hZout (hEout u hu) (hEout u0 hu0)).2
      have himg_card : ((A w).image l).card ≤ 1 :=
        (Finset.card_le_card himg_sub).trans (by simp)
      omega
    · simp only [Finset.not_nonempty_iff_eq_empty] at hne
      rw [hne]
      simp
  have hsub : ∀ w : Fin m, D (U w) (S w) T gates ⊆ (Finset.Ico n (n + gates.length)).erase (n + i0.val) := by
    intro w i hi
    simp only [D, Finset.mem_filter, Finset.mem_Ico] at hi
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_Ico.mpr hi.1⟩
    intro heq
    have hfalse : val gates (Zof (S w) T) (n + i0.val) = false := heq ▸ hi.2.1
    rw [hi0_true w] at hfalse
    exact absurd hfalse (by decide)
  have hdisj : ∀ w1 w2 : Fin m, w1 ≠ w2 → Disjoint (D (U w1) (S w1) T gates) (D (U w2) (S w2) T gates) := by
    intro w1 w2 hne
    rw [Finset.disjoint_left]
    intro i hi1 hi2
    obtain ⟨l1, hinv1, -⟩ := hinv_all w1
    obtain ⟨l2, hinv2, -⟩ := hinv_all w2
    simp only [D, Finset.mem_filter] at hi1 hi2
    obtain ⟨hz1, u1, v1, hu1U1, hv1U1, huv1, hu1, hv1⟩ := hi1.2
    obtain ⟨hz2, u2, v2, hu2U2, hv2U2, huv2, hu2, hv2⟩ := hi2.2
    have hcontra : ∀ u v : Fin n, u ≠ v → u ∈ S w1 → v ∈ S w1 → u ∈ S w2 → v ∈ S w2 → False := by
      intro u v huv hu1S hv1S hu2S hv2S
      have hpair : ({u, v} : Finset (Fin n)) ⊆ S w1 ∩ S w2 := by
        intro z hz
        rcases Finset.mem_insert.mp hz with rfl | hz
        · exact Finset.mem_inter.mpr ⟨hu1S, hu2S⟩
        · rw [Finset.mem_singleton.mp hz]
          exact Finset.mem_inter.mpr ⟨hv1S, hv2S⟩
      have h2 : 2 ≤ (S w1 ∩ S w2).card := by
        have hc : ({u, v} : Finset (Fin n)).card = 2 := Finset.card_pair huv
        rw [← hc]
        exact Finset.card_le_card hpair
      have h1 := hSinter w1 w2 hne
      omega
    by_cases ht0w1 : t0 ∈ S w1
    · have hU2subU1 : U w2 ⊆ U w1 := by
        intro z hz
        simp only [U, ite_eq_left ht0w1, Finset.mem_sdiff, Finset.mem_univ, true_and]
        by_cases ht0w2 : t0 ∈ S w2
        · simpa [U, ht0w2] using hz
        · simp only [U, ite_eq_right ht0w2, Finset.mem_sdiff, Finset.mem_univ, true_and] at hz
          exact fun h' => hz (Finset.mem_of_mem_erase h')
      have hu2A1 := (hinv1 i u2 v2 (hU2subU1 hu2U2) (hU2subU1 hv2U2) hz1 hu2 hv2).1
      have hv2A1 := (hinv1 i v2 u2 (hU2subU1 hv2U2) (hU2subU1 hu2U2) hz1 hv2 hu2).1
      have hu2A2 := (hinv2 i u2 v2 hu2U2 hv2U2 hz2 hu2 hv2).1
      have hv2A2 := (hinv2 i v2 u2 hv2U2 hu2U2 hz2 hv2 hu2).1
      exact hcontra u2 v2 huv2 (Finset.mem_sdiff.mp hu2A1).1 (Finset.mem_sdiff.mp hv2A1).1
        (Finset.mem_sdiff.mp hu2A2).1 (Finset.mem_sdiff.mp hv2A2).1
    · have hU1subU2 : U w1 ⊆ U w2 := by
        intro z hz
        simp only [U, ite_eq_right ht0w1, Finset.mem_sdiff, Finset.mem_univ, true_and] at hz
        by_cases ht0w2 : t0 ∈ S w2
        · simp only [U, ite_eq_left ht0w2, Finset.mem_sdiff, Finset.mem_univ, true_and]
          exact fun h' => hz (Finset.mem_of_mem_erase h')
        · simp [U, ht0w2, hz]
      have hu1A1 := (hinv1 i u1 v1 hu1U1 hv1U1 hz1 hu1 hv1).1
      have hv1A1 := (hinv1 i v1 u1 hv1U1 hu1U1 hz1 hv1 hu1).1
      have hu1A2 := (hinv2 i u1 v1 (hU1subU2 hu1U1) (hU1subU2 hv1U1) hz2 hu1 hv1).1
      have hv1A2 := (hinv2 i v1 u1 (hU1subU2 hv1U1) (hU1subU2 hu1U1) hz2 hv1 hu1).1
      exact hcontra u1 v1 huv1 (Finset.mem_sdiff.mp hu1A1).1 (Finset.mem_sdiff.mp hv1A1).1
        (Finset.mem_sdiff.mp hu1A2).1 (Finset.mem_sdiff.mp hv1A2).1
  have hsum_D : ∑ w : Fin m, (D (U w) (S w) T gates).card ≤ gates.length - 1 := by
    have hbiUnion : (Finset.univ.biUnion fun w : Fin m => D (U w) (S w) T gates) ⊆
        (Finset.Ico n (n + gates.length)).erase (n + i0.val) := by
      intro i hi
      obtain ⟨w, _, hw⟩ := Finset.mem_biUnion.mp hi
      exact hsub w hw
    have hcard_eq : (Finset.univ.biUnion fun w : Fin m => D (U w) (S w) T gates).card =
        ∑ w : Fin m, (D (U w) (S w) T gates).card :=
      Finset.card_biUnion fun w1 _ w2 _ hne => hdisj w1 w2 hne
    have hcard_erase : ((Finset.Ico n (n + gates.length)).erase (n + i0.val)).card = gates.length - 1 := by
      have hmem : n + i0.val ∈ Finset.Ico n (n + gates.length) := by
        simp [i0.isLt]
      rw [Finset.card_erase_of_mem hmem, Nat.card_Ico]
      omega
    rw [← hcard_eq, ← hcard_erase]
    exact Finset.card_le_card hbiUnion
  have hsum_A : 1 + ∑ w : Fin m, ((A w).card - 1) ≤ gates.length := by
    have h1 : ∑ w : Fin m, ((A w).card - 1) ≤ ∑ w : Fin m, (D (U w) (S w) T gates).card :=
      Finset.sum_le_sum fun w _ => hbound w
    have hpos : 1 ≤ gates.length := Nat.succ_le_of_lt (Nat.pos_of_ne_zero (by have := i0.isLt; omega))
    omega
  have hsplit_S : ∀ w : Fin m, (S w).card - 1 ≤ ((A w).card - 1) + (S w ∩ T').card := by
    intro w
    have hcard : (A w).card + (S w ∩ T').card = (S w).card := by
      simp [A]
    omega
  have hsum_S : ∑ w : Fin m, ((S w).card - 1) ≤
      (∑ w : Fin m, ((A w).card - 1)) + ∑ w : Fin m, (S w ∩ T').card := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun w _ => hsplit_S w
  have hdouble : ∑ w : Fin m, (S w ∩ T').card =
      ∑ u ∈ T', (Finset.univ.filter (fun c : Fin m => u ∈ S c)).card := by
    have h1 : ∀ w : Fin m, (S w ∩ T').card = ∑ u ∈ T', if u ∈ S w then 1 else 0 := by
      intro w
      rw [Finset.sum_boole, Nat.cast_id]
      congr 1
      ext u
      simp [Finset.mem_inter, and_comm]
    have h2 : ∀ u ∈ T', (Finset.univ.filter (fun c : Fin m => u ∈ S c)).card =
        ∑ w : Fin m, if u ∈ S w then 1 else 0 := by
      intro u _
      rw [Finset.sum_boole, Nat.cast_id]
    simp_rw [h1]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun u hu => (h2 u hu).symm
  change 1 + ∑ s : Fin m, ((S s).card - 1) ≤ gates.length + ∑ u ∈ T', (Finset.univ.filter (fun c : Fin m => u ∈ S c)).card
  omega

end PEqualNP.Outside.L_meta_986

theorem PEqualNP.Outside.L_meta_986 : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)) (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ) (i0 : Fin gates.length) (hw : ℕ) (T : Finset (Fin n)) (t0 : Fin n), (∀ i : Fin m, 2 ≤ (S i).card) → (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ q : Fin gates.length, (gates.get q).op = PEqualNP.CircuitLowerBounds.GateOp.not → q = i0) → (gates.get i0).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get i0).inputs.head? = some hw → hw < n + i0.val → (∀ (o : Fin m) (x : Fin n → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out o⟩ (List.ofFn x) = decide (∃ v ∈ S o, x v = true)) → (∀ y : Fin n → Bool, (∀ t ∈ T, y t = false) → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, hw⟩ (List.ofFn y) = false) → t0 ∈ T → (∀ t ∈ T, (Finset.univ.filter (fun a : Fin m => t ∈ S a)).card ≤ (Finset.univ.filter (fun b : Fin m => t0 ∈ S b)).card) → 1 + ∑ s : Fin m, ((S s).card - 1) ≤ gates.length + ∑ u ∈ T.erase t0, (Finset.univ.filter (fun c : Fin m => u ∈ S c)).card :=
  PEqualNP.Outside.L_meta_986.main_proof
