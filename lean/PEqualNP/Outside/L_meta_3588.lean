import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3588

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- wr_*, neg_step and bin_step adapted from L_meta_2683 (Apache-2.0)
def wr (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

theorem wr_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    wr (gs ++ [g]) x = wr gs x ++ [g.op.eval (g.inputs.map fun i => (wr gs x).getD i false)] := by
  simp [wr, List.foldl_append]

theorem wr_len (gs : List Gate) (x : List Bool) : (wr gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [wr]
  | append_singleton l a ih => rw [wr_snoc]; simp [ih]; omega

theorem wr_old (gs : List Gate) (g : Gate) (x : List Bool) (i : ℕ)
    (h : i < x.length + gs.length) :
    (wr (gs ++ [g]) x).getD i false = (wr gs x).getD i false := by
  rw [wr_snoc]
  exact List.getD_append _ _ _ _ (by rw [wr_len]; exact h)

theorem wr_new (gs : List Gate) (g : Gate) (x : List Bool) (n : ℕ) (h : x.length = n) :
    (wr (gs ++ [g]) x).getD (n + gs.length) false
      = g.op.eval (g.inputs.map fun i => (wr gs x).getD i false) := by
  subst h
  rw [wr_snoc, List.getD_append_right _ _ _ _ (by rw [wr_len]), wr_len]
  simp

theorem wr_big (gs : List Gate) (x : List Bool) (i : ℕ) (h : x.length + gs.length ≤ i) :
    (wr gs x).getD i false = false :=
  List.getD_eq_default _ _ (by rw [wr_len]; exact h)

def At (hs : List Gate) (f : (Fin 8 → Bool) → Bool) (i : ℕ) : Prop :=
  i < 8 + hs.length ∧ ∀ y, (wr hs (List.ofFn y)).getD i false = f y

def Ok (hs : List Gate) (f : (Fin 8 → Bool) → Bool) : Prop :=
  (∃ b, ∀ y, f y = b) ∨ ∃ i, At hs f i

theorem ok_old {hs : List Gate} {f : (Fin 8 → Bool) → Bool} (g : Gate) (h : Ok hs f) :
    Ok (hs ++ [g]) f := by
  rcases h with h | ⟨i, hi, h⟩
  · exact Or.inl h
  · refine Or.inr ⟨i, by simp; omega, fun y => ?_⟩
    rw [wr_old hs g _ i (by simpa using hi), h y]

theorem ok_new {hs : List Gate} {f : (Fin 8 → Bool) → Bool} (g : Gate)
    (h : ∀ y, g.op.eval (g.inputs.map fun i => (wr hs (List.ofFn y)).getD i false) = f y) :
    Ok (hs ++ [g]) f :=
  Or.inr ⟨8 + hs.length, by simp, fun y => by rw [wr_new hs g _ 8 (by simp), h y]⟩

def Two (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

theorem two_snoc {hs : List Gate} {g : Gate} (h : ∀ g ∈ hs, Two g) (hg : Two g) :
    ∀ g' ∈ hs ++ [g], Two g' := by
  intro g' h'
  rcases List.mem_append.1 h' with h' | h'
  · exact h g' h'
  · rw [List.mem_singleton.1 h']; exact hg

theorem neg_step {hs : List Gate} {f : (Fin 8 → Bool) → Bool} (h : Ok hs f) :
    ∃ g, Two g ∧ Ok (hs ++ [g]) (fun y => !(f y)) := by
  rcases h with ⟨b, hb⟩ | ⟨i, hi, h⟩
  · refine ⟨⟨GateOp.or, []⟩, by simp [Two], Or.inl ⟨!b, fun y => ?_⟩⟩
    simp only [hb y]
  · refine ⟨⟨GateOp.not, [i]⟩, by simp [Two], ok_new _ fun y => ?_⟩
    simp only [List.map, GateOp.eval, List.headD_cons, h y]

theorem triv_step {hs : List Gate} {f : (Fin 8 → Bool) → Bool} (h : Ok hs f) :
    ∃ g, Two g ∧ Ok (hs ++ [g]) f :=
  ⟨⟨GateOp.or, []⟩, by simp [Two], ok_old _ h⟩

theorem ok_congr {hs : List Gate} {f f' : (Fin 8 → Bool) → Bool} (h : Ok hs f)
    (e : ∀ y, f' y = f y) : Ok hs f' := by
  rw [funext e]; exact h

theorem and_step {hs : List Gate} {f f' : (Fin 8 → Bool) → Bool}
    (h : Ok hs f) (h' : Ok hs f') :
    ∃ g, Two g ∧ Ok (hs ++ [g]) (fun y => f y && f' y) := by
  rcases id h with ⟨b, hb⟩ | ⟨i, hi, hh⟩
  · cases b
    · exact triv_step (Or.inl ⟨false, fun y => by simp [hb y]⟩)
    · exact triv_step (ok_congr h' fun y => by simp [hb y])
  · rcases id h' with ⟨b, hb⟩ | ⟨j, hj, hh'⟩
    · cases b
      · exact triv_step (Or.inl ⟨false, fun y => by simp [hb y]⟩)
      · exact triv_step (ok_congr h fun y => by simp [hb y])
    · refine ⟨⟨GateOp.and, [i, j]⟩, by simp [Two], ok_new _ fun y => ?_⟩
      simp only [List.map, GateOp.eval, hh y, hh' y]; simp

theorem or_step {hs : List Gate} {f f' : (Fin 8 → Bool) → Bool}
    (h : Ok hs f) (h' : Ok hs f') :
    ∃ g, Two g ∧ Ok (hs ++ [g]) (fun y => f y || f' y) := by
  rcases id h with ⟨b, hb⟩ | ⟨i, hi, hh⟩
  · cases b
    · exact triv_step (ok_congr h' fun y => by simp [hb y])
    · exact triv_step (Or.inl ⟨true, fun y => by simp [hb y]⟩)
  · rcases id h' with ⟨b, hb⟩ | ⟨j, hj, hh'⟩
    · cases b
      · exact triv_step (ok_congr h fun y => by simp [hb y])
      · exact triv_step (Or.inl ⟨true, fun y => by simp [hb y]⟩)
    · refine ⟨⟨GateOp.or, [i, j]⟩, by simp [Two], ok_new _ fun y => ?_⟩
      simp only [List.map, GateOp.eval, hh y, hh' y]; simp

theorem shape {l : List ℕ} (h : l.length ≤ 2) :
    l = [] ∨ (∃ a, l = [a]) ∨ ∃ a b, l = [a, b] := by
  match l, h with
  | [], _ => exact Or.inl rfl
  | [a], _ => exact Or.inr (Or.inl ⟨a, rfl⟩)
  | [a, b], _ => exact Or.inr (Or.inr ⟨a, b, rfl⟩)

-- one gate per gate
theorem gate_step {hs : List Gate} (v : (Fin 8 → Bool) → ℕ → Bool)
    (hv : ∀ i, Ok hs (fun y => v y i)) (g : Gate) (hg : Two g) :
    ∃ g', Two g' ∧ Ok (hs ++ [g']) (fun y => g.op.eval (g.inputs.map (v y))) := by
  obtain ⟨op, l⟩ := g
  obtain ⟨ho, hl⟩ := hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ho
  simp only at hl
  rcases shape hl with rfl | ⟨a, rfl⟩ | ⟨a, b, rfl⟩
  · exact triv_step (Or.inl ⟨op.eval [], fun y => by simp⟩)
  · rcases ho with rfl | rfl | rfl
    · exact triv_step (ok_congr (hv a) fun y => by simp [GateOp.eval])
    · exact triv_step (ok_congr (hv a) fun y => by simp [GateOp.eval])
    · obtain ⟨g, h2, h⟩ := neg_step (hv a)
      exact ⟨g, h2, ok_congr h fun y => by simp [GateOp.eval]⟩
  · rcases ho with rfl | rfl | rfl
    · obtain ⟨g, h2, h⟩ := and_step (hv a) (hv b)
      exact ⟨g, h2, ok_congr h fun y => by simp [GateOp.eval]⟩
    · obtain ⟨g, h2, h⟩ := or_step (hv a) (hv b)
      exact ⟨g, h2, ok_congr h fun y => by simp [GateOp.eval]⟩
    · obtain ⟨g, h2, h⟩ := neg_step (hv a)
      exact ⟨g, h2, ok_congr h fun y => by simp [GateOp.eval]⟩

-- a gate either is free or keeps equality of two assignments outside D
theorem free_step {hs : List Gate} (v : (Fin 8 → Bool) → ℕ → Bool) (D : ℕ → Prop)
    (hv : ∀ i, Ok hs (fun y => v y i)) (hD : ∀ i, D i → ∀ y, v y i = false)
    (p q : ℕ → Bool) (hpq : ∀ i, ¬ D i → p i = q i) (g : Gate) (hg : Two g) :
    Ok hs (fun y => g.op.eval (g.inputs.map (v y))) ∨
      g.op.eval (g.inputs.map p) = g.op.eval (g.inputs.map q) := by
  obtain ⟨op, l⟩ := g
  obtain ⟨ho, hl⟩ := hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ho
  simp only at hl
  rcases shape hl with rfl | ⟨a, rfl⟩ | ⟨a, b, rfl⟩
  · exact Or.inr rfl
  · by_cases ha : D a
    · exact Or.inl (Or.inl ⟨op.eval [false], fun y => by simp [hD a ha y]⟩)
    · exact Or.inr (by simp [hpq a ha])
  · rcases ho with rfl | rfl | rfl
    · by_cases ha : D a
      · exact Or.inl (Or.inl ⟨false, fun y => by simp [GateOp.eval, hD a ha y]⟩)
      · by_cases hb : D b
        · exact Or.inl (Or.inl ⟨false, fun y => by simp [GateOp.eval, hD b hb y]⟩)
        · exact Or.inr (by simp [hpq a ha, hpq b hb])
    · by_cases ha : D a
      · exact Or.inl (ok_congr (hv b) fun y => by simp [GateOp.eval, hD a ha y])
      · by_cases hb : D b
        · exact Or.inl (ok_congr (hv a) fun y => by simp [GateOp.eval, hD b hb y])
        · exact Or.inr (by simp [hpq a ha, hpq b hb])
    · by_cases ha : D a
      · exact Or.inl (Or.inl ⟨true, fun y => by simp [GateOp.eval, hD a ha y]⟩)
      · exact Or.inr (by simp [GateOp.eval, hpq a ha])

theorem build (B : (Fin 8 → Bool) → List Bool) (P Q : List Bool) (D : ℕ → Prop)
    (hB : ∀ y, (B y).length = 11) (hP : P.length = 11) (hQ : Q.length = 11)
    (hD11 : ∀ i, D i → i < 11) (hD : ∀ i, D i → ∀ y, (B y).getD i false = false)
    (h0 : ∀ i, Ok [] (fun y => (B y).getD i false))
    (hpq : ∀ i, ¬ D i → P.getD i false = Q.getD i false) (gs : List Gate) :
    (∀ g ∈ gs, Two g) →
    ∃ hs : List Gate, (∀ g ∈ hs, Two g) ∧ (∀ i, Ok hs (fun y => (wr gs (B y)).getD i false)) ∧
      (∀ i, D i → ∀ y, (wr gs (B y)).getD i false = false) ∧
      (hs.length + 1 ≤ gs.length ∨ (hs.length ≤ gs.length ∧
        ∀ i, ¬ D i → (wr gs P).getD i false = (wr gs Q).getD i false)) := by
  induction gs using List.reverseRecOn with
  | nil =>
    exact fun _ => ⟨[], by simp, h0, hD, Or.inr ⟨le_rfl, hpq⟩⟩
  | append_singleton l g ih =>
    intro hg
    obtain ⟨hs, h2, hv, hd, hc⟩ := ih fun g hg' => hg g (List.mem_append_left _ hg')
    have hgg : Two g := hg g (by simp)
    have hd' : ∀ i, D i → ∀ y, (wr (l ++ [g]) (B y)).getD i false = false := by
      intro i hi y
      rw [wr_old _ _ _ _ (by rw [hB]; have := hD11 i hi; omega)]
      exact hd i hi y
    have hall : ∀ hs' : List Gate, (∀ i, Ok hs' (fun y => (wr l (B y)).getD i false)) →
        Ok hs' (fun y => g.op.eval (g.inputs.map fun i => (wr l (B y)).getD i false)) →
        ∀ i, Ok hs' (fun y => (wr (l ++ [g]) (B y)).getD i false) := by
      intro hs' h1 h3 i
      rcases lt_trichotomy i (11 + l.length) with h | h | h
      · exact ok_congr (h1 i) fun y => wr_old _ _ _ _ (by rw [hB]; exact h)
      · subst h
        exact ok_congr h3 fun y => wr_new _ _ _ _ (hB y)
      · exact Or.inl ⟨false, fun y => wr_big _ _ _ (by rw [hB]; simp; omega)⟩
    have hgen : ∃ g', Two g' ∧ ∀ i, Ok (hs ++ [g'])
        (fun y => (wr (l ++ [g]) (B y)).getD i false) := by
      obtain ⟨g', ht, h3⟩ := gate_step _ hv g hgg
      exact ⟨g', ht, hall _ (fun i => ok_old g' (hv i)) h3⟩
    rcases hc with hc | ⟨hc, he⟩
    · obtain ⟨g', ht, h3⟩ := hgen
      exact ⟨hs ++ [g'], two_snoc h2 ht, h3, hd', Or.inl (by simp; omega)⟩
    · rcases free_step _ D hv hd (fun i => (wr l P).getD i false)
        (fun i => (wr l Q).getD i false) he g hgg with hf | hf
      · exact ⟨hs, h2, hall _ hv hf, hd', Or.inl (by simp; omega)⟩
      · obtain ⟨g', ht, h3⟩ := hgen
        refine ⟨hs ++ [g'], two_snoc h2 ht, h3, hd', Or.inr ⟨by simp; omega, fun i hi => ?_⟩⟩
        rcases lt_trichotomy i (11 + l.length) with h | h | h
        · rw [wr_old _ _ _ _ (by rw [hP]; exact h), wr_old _ _ _ _ (by rw [hQ]; exact h)]
          exact he i hi
        · subst h
          rw [wr_new _ _ _ _ hP, wr_new _ _ _ _ hQ]
          exact hf
        · rw [wr_big _ _ _ (by rw [hP]; simp; omega), wr_big _ _ _ (by rw [hQ]; simp; omega)]

def ins (y : Fin 8 → Bool) : Fin 9 → Bool := ![y 0, y 1, y 2, y 3, false, y 4, y 5, y 6, y 7]

def six (x : Fin 9 → Bool) : List Bool := List.ofFn x ++ [x 0 || x 4]

def bs (k : ℕ) (x : Fin 9 → Bool) : List Bool := six x ++ [(six x).getD k false]

theorem six_len (x : Fin 9 → Bool) : (six x).length = 10 := by simp [six]

theorem bs_len (k : ℕ) (x : Fin 9 → Bool) : (bs k x).length = 11 := by simp [bs, six]

theorem six_lt (x : Fin 9 → Bool) (i : Fin 9) : (six x).getD i false = x i := by
  unfold six
  rw [List.getD_append _ _ _ _ (by simp)]
  fin_cases i <;> rfl

theorem six_nine (x : Fin 9 → Bool) : (six x).getD 9 false = (x 0 || x 4) := by
  unfold six
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp

theorem six_big (x : Fin 9 → Bool) (i : ℕ) (h : 10 ≤ i) : (six x).getD i false = false :=
  List.getD_eq_default _ _ (by rw [six_len]; exact h)

theorem bs_lt (k : ℕ) (x : Fin 9 → Bool) (i : ℕ) (h : i < 10) :
    (bs k x).getD i false = (six x).getD i false :=
  List.getD_append _ _ _ _ (by rw [six_len]; exact h)

theorem bs_ten (k : ℕ) (x : Fin 9 → Bool) :
    (bs k x).getD 10 false = (six x).getD k false := by
  unfold bs
  rw [List.getD_append_right _ _ _ _ (by rw [six_len]), six_len]
  simp

theorem bs_big (k : ℕ) (x : Fin 9 → Bool) (i : ℕ) (h : 11 ≤ i) : (bs k x).getD i false = false :=
  List.getD_eq_default _ _ (by rw [bs_len]; exact h)

theorem inp (j : Fin 8) : Ok [] (fun y => y j) :=
  Or.inr ⟨j, by simp, fun y => by fin_cases j <;> rfl⟩

theorem six_ok (i : ℕ) : Ok [] (fun y => (six (ins y)).getD i false) := by
  by_cases h : i < 9
  · obtain ⟨j, rfl⟩ : ∃ j : Fin 9, i = j := ⟨⟨i, h⟩, rfl⟩
    refine ok_congr (f := fun y => ins y j) ?_ fun y => six_lt _ j
    fin_cases j
    · exact inp 0
    · exact inp 1
    · exact inp 2
    · exact inp 3
    · exact Or.inl ⟨false, fun y => rfl⟩
    · exact inp 4
    · exact inp 5
    · exact inp 6
    · exact inp 7
  · by_cases h' : i = 9
    · subst h'
      refine ok_congr (inp 0) fun y => ?_
      rw [six_nine]
      simp [ins]
    · exact Or.inl ⟨false, fun y => six_big _ _ (by omega)⟩

theorem bs_ok (k i : ℕ) : Ok [] (fun y => (bs k (ins y)).getD i false) := by
  rcases lt_trichotomy i 10 with h | h | h
  · exact ok_congr (six_ok i) fun y => bs_lt _ _ _ h
  · subst h
    exact ok_congr (six_ok k) fun y => bs_ten _ _
  · exact Or.inl ⟨false, fun y => bs_big _ _ _ h⟩

theorem six_four (y : Fin 8 → Bool) : (six (ins y)).getD 4 false = false :=
  (six_lt (ins y) 4).trans rfl

theorem six_eq (x : Fin 9 → Bool) (hx : x 0 = true) (i : ℕ) (hi : i ≠ 4) :
    (six x).getD i false = (six (Function.update x 4 true)).getD i false := by
  by_cases h : i < 9
  · obtain ⟨j, rfl⟩ : ∃ j : Fin 9, i = j := ⟨⟨i, h⟩, rfl⟩
    rw [six_lt, six_lt, Function.update_of_ne]
    rintro rfl
    exact hi rfl
  · by_cases h' : i = 9
    · subst h'
      rw [six_nine, six_nine]
      simp [hx]
    · rw [six_big _ _ (by omega), six_big _ _ (by omega)]

theorem main (x1 : Circuit) (k : ℕ) (f : (Fin 9 → Bool) → Bool) (h2 : FanInTwo x1)
    (hf : ∀ x, x1.eval (bs k x) = f x) (x : Fin 9 → Bool) (hx : x 0 = true)
    (hne : f x ≠ f (Function.update x 4 true)) (u v : Fin 8 → Bool)
    (huv : f (ins u) ≠ f (ins v)) :
    HasCircuitSize 8 (fun y => f (ins y)) (x1.size - 1) := by
  obtain ⟨hs, ht, hv, hd, hc⟩ := build (fun y => bs k (ins y)) (bs k x)
    (bs k (Function.update x 4 true)) (fun i => i = 4 ∨ (i = 10 ∧ k = 4))
    (fun y => bs_len _ _) (bs_len _ _) (bs_len _ _) (fun i h => by omega)
    (by
      rintro i (rfl | ⟨rfl, rfl⟩) y
      · rw [bs_lt _ _ _ (by omega)]; exact six_four y
      · rw [bs_ten]; exact six_four y)
    (bs_ok k)
    (by
      intro i hi
      rcases lt_trichotomy i 10 with h | h | h
      · rw [bs_lt _ _ _ h, bs_lt _ _ _ h]
        exact six_eq x hx i (by omega)
      · subst h
        rw [bs_ten, bs_ten]
        exact six_eq x hx k (by omega)
      · rw [bs_big _ _ _ h, bs_big _ _ _ h])
    x1.gates h2
  have hf' : ∀ x, (wr x1.gates (bs k x)).getD x1.output false = f x := hf
  rcases hc with hc | ⟨_, he⟩
  · rcases hv x1.output with ⟨b, hb⟩ | ⟨i, hi, hA⟩
    · exfalso
      apply huv
      rw [← hf', ← hf']
      exact (hb u).trans (hb v).symm
    · refine ⟨⟨hs, i⟩, ht, ?_, fun y => ?_⟩
      · change hs.length ≤ x1.gates.length - 1
        omega
      · exact (hA y).trans (hf' _)
  · exfalso
    by_cases hD : x1.output = 4 ∨ (x1.output = 10 ∧ k = 4)
    · apply huv
      rw [← hf', ← hf']
      exact (hd _ hD u).trans (hd _ hD v).symm
    · apply hne
      rw [← hf', ← hf']
      exact he _ hD

end PEqualNP.Outside.L_meta_3588

theorem PEqualNP.Outside.L_meta_3588 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (11 : ℕ)) (x3 : (Fin (9 : ℕ) → Bool) → Bool),   PEqualNP.MetaComplexity.FanInTwo x1 →     (∀ (x5 : Fin (9 : ℕ) → Bool),         have x6 : List Bool := List.ofFn x5 ++ [x5 (0 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ))];         x1.eval (x6 ++ [x6.getD (↑x2) Bool.false]) = x3 x5) →       (∃ (x6 : Fin (9 : ℕ) → Bool), x6 (0 : Fin (9 : ℕ)) = Bool.true ∧ x6 (4 : Fin (9 : ℕ)) = Bool.false ∧ x3 x6 ≠ x3 (Function.update x6 (4 : Fin (9 : ℕ)) Bool.true)) →         have x7 : (Fin (8 : ℕ) → Bool) → Bool := fun (x7 : Fin (8 : ℕ) → Bool) => x3 ![x7 (0 : Fin (8 : ℕ)), x7 (1 : Fin (8 : ℕ)), x7 (2 : Fin (8 : ℕ)), x7 (3 : Fin (8 : ℕ)), Bool.false, x7 (4 : Fin (8 : ℕ)), x7 (5 : Fin (8 : ℕ)), x7 (6 : Fin (8 : ℕ)), x7 (7 : Fin (8 : ℕ))];         (∃ (x8 : Fin (8 : ℕ) → Bool) (x9 : Fin (8 : ℕ) → Bool), x7 x8 ≠ x7 x9) → PEqualNP.MetaComplexity.HasCircuitSize (8 : ℕ) x7 (x1.size - (1 : ℕ)) := by
  intro x1 x2 x3 h2 hf hx x7 hn
  obtain ⟨x, hx, _, hne⟩ := hx
  obtain ⟨u, v, huv⟩ := hn
  exact PEqualNP.Outside.L_meta_3588.main x1 x2 x3 h2 hf x hx hne u v huv
