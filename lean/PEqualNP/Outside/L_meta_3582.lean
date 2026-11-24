import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3582

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- wr_* adapted from L_meta_2683 (Apache-2.0)
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

theorem wr_low (gs : List Gate) (x : List Bool) (i : ℕ) (h : i < x.length) :
    (wr gs x).getD i false = x.getD i false := by
  induction gs using List.reverseRecOn with
  | nil => rfl
  | append_singleton l g ih => rw [wr_old _ _ _ _ (by omega), ih]

-- two runs that differ only on the wires in D
theorem sim (n : ℕ) (X Y : List Bool) (D : ℕ → Prop) (hD : ∀ i, D i → i < n) (hX : X.length = n)
    (hY : Y.length = n) (h0 : ∀ i, ¬ D i → X.getD i false = Y.getD i false) (gs : List Gate) :
    (∀ g ∈ gs, ∀ u v : ℕ → Bool, (∀ i, ¬ D i → u i = v i) →
      (∀ i, i < n → u i = X.getD i false) → (∀ i, i < n → v i = Y.getD i false) →
      g.op.eval (g.inputs.map u) = g.op.eval (g.inputs.map v)) →
    ∀ i, ¬ D i → (wr gs X).getD i false = (wr gs Y).getD i false := by
  induction gs using List.reverseRecOn with
  | nil => exact fun _ => h0
  | append_singleton l g ih =>
    intro hg i hi
    have ih := ih fun g' h' => hg g' (List.mem_append_left _ h')
    rcases lt_trichotomy i (n + l.length) with h | h | h
    · rw [wr_old _ _ _ _ (by rw [hX]; exact h), wr_old _ _ _ _ (by rw [hY]; exact h)]
      exact ih i hi
    · subst h
      rw [wr_new _ _ _ _ hX, wr_new _ _ _ _ hY]
      exact hg g (by simp) _ _ ih (fun i h => wr_low _ _ _ (by rw [hX]; exact h))
        (fun i h => wr_low _ _ _ (by rw [hY]; exact h))
    · rw [wr_big _ _ _ (by rw [hX]; simp; omega), wr_big _ _ _ (by rw [hY]; simp; omega)]

def f (x : Fin 9 → Bool) : Bool :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 ||
  x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5

def bits (n : Fin 512) : Fin 9 → Bool := fun i => n.val.testBit i.val

def ext (x : Fin 9 → Bool) : List Bool := List.ofFn x ++ [x 0 || x 2]

theorem ext_len (x : Fin 9 → Bool) : (ext x).length = 10 := by simp [ext]

theorem ext_lt (x : Fin 9 → Bool) (i : Fin 9) : (ext x).getD i false = x i := by
  unfold ext
  rw [List.getD_append _ _ _ _ (by simp)]
  fin_cases i <;> rfl

theorem ext_nine (x : Fin 9 → Bool) : (ext x).getD 9 false = (x 0 || x 2) := by
  unfold ext
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp

theorem ext_eq (x y : Fin 9 → Bool) (D : ℕ → Prop) (h9 : (x 0 || x 2) = (y 0 || y 2))
    (h : ∀ i : Fin 9, ¬ D i → x i = y i) (i : ℕ) (hi : ¬ D i) :
    (ext x).getD i false = (ext y).getD i false := by
  rcases lt_trichotomy i 9 with q | q | q
  · rw [ext_lt x ⟨i, q⟩, ext_lt y ⟨i, q⟩]
    exact h ⟨i, q⟩ hi
  · subst q
    rw [ext_nine, ext_nine, h9]
  · rw [List.getD_eq_default _ _ (by rw [ext_len]; exact q),
      List.getD_eq_default _ _ (by rw [ext_len]; exact q)]

def flip (i : Fin 9) (x : Fin 9 → Bool) : Fin 9 → Bool :=
  fun k => if k = i then !(x k) else x k

def w10 (x : Fin 9 → Bool) (j : Fin 10) : Bool :=
  if h : j.val < 9 then x ⟨j.val, h⟩ else x 0 || x 2

theorem ext_w10 (x : Fin 9 → Bool) (j : Fin 10) : (ext x).getD j false = w10 x j := by
  unfold w10
  split_ifs with h
  · exact ext_lt x ⟨j.val, h⟩
  · rw [show (j : ℕ) = 9 by omega]
    exact ext_nine x

theorem wit : ∀ i : Fin 9, i ≠ 0 → i ≠ 2 → ∀ j : Fin 10, i.castSucc ≠ j → ∀ c : Bool,
    ∃ n : Fin 512, w10 (bits n) j = c ∧ f (bits n) ≠ f (flip i (bits n)) := by decide +kernel

theorem wit0 : ∀ i : Fin 9, ∃ n : Fin 512, bits n i ≠ f (bits n) := by decide +kernel

def rd (g : Gate) : List ℕ :=
  List.take (bif g.op.eval [false] then 1 else 2) g.inputs

theorem avoid (g : Gate) (hg : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (h2 : g.inputs.length ≤ 2) (u v : ℕ → Bool) (h : ∀ i ∈ rd g, u i = v i) :
    g.op.eval (g.inputs.map u) = g.op.eval (g.inputs.map v) := by
  obtain ⟨op, l⟩ := g
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  simp only at h2
  rcases hg with rfl | rfl | rfl
  · have : rd ⟨GateOp.and, l⟩ = l := List.take_of_length_le h2
    rw [this] at h
    simp only
    rw [List.map_congr_left h]
  · have : rd ⟨GateOp.or, l⟩ = l := List.take_of_length_le h2
    rw [this] at h
    simp only
    rw [List.map_congr_left h]
  · cases l with
    | nil => rfl
    | cons a l =>
      have : u a = v a := h a (by simp [rd, GateOp.eval])
      simp [GateOp.eval, this]

theorem main (C : Circuit) (h2 : FanInTwo C) (hf : ∀ x, C.eval (ext x) = f x) (i : Fin 9)
    (j : Fin 10) (h0 : i ≠ 0) (h02 : i ≠ 2) (hij : i.castSucc ≠ j) (g : Gate) (hg : g ∈ C.gates)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    (hl : g.inputs = [(i : ℕ), (j : ℕ)] ∨ g.inputs = [(j : ℕ), (i : ℕ)]) :
    2 ≤ (C.gates.filter fun g => (rd g).contains (i : ℕ)).length := by
  by_contra! hc
  have hgi : (rd g).contains (i : ℕ) = true := by
    obtain ⟨op, l⟩ := g
    simp only at hop hl
    rcases hop with rfl | rfl <;> rcases hl with rfl | rfl <;> simp [rd, GateOp.eval]
  obtain ⟨l1, l2, hs⟩ := List.append_of_mem hg
  have hav : ∀ g' ∈ l1 ++ l2, (i : ℕ) ∉ rd g' := by
    rw [hs, List.filter_append, List.filter_cons_of_pos (by simpa using hgi), List.length_append,
      List.length_cons] at hc
    intro g' hg' hm
    rcases List.mem_append.1 hg' with q | q
    · have : 0 < (l1.filter fun g => (rd g).contains (i : ℕ)).length :=
        List.length_pos_of_mem (List.mem_filter.2 ⟨q, by simpa using hm⟩)
      omega
    · have : 0 < (l2.filter fun g => (rd g).contains (i : ℕ)).length :=
        List.length_pos_of_mem (List.mem_filter.2 ⟨q, by simpa using hm⟩)
      omega
  obtain ⟨c, hcv⟩ : ∃ c : Bool, ∀ p q : Bool, g.op.eval [p, c] = g.op.eval [q, c] ∧
      g.op.eval [c, p] = g.op.eval [c, q] := by
    rcases hop with e | e <;> rw [e]
    · exact ⟨false, by decide⟩
    · exact ⟨true, by decide⟩
  obtain ⟨n, hj, hne⟩ := wit i h0 h02 j hij c
  have hout : C.output ≠ i := by
    intro e
    obtain ⟨n, hn⟩ := wit0 i
    apply hn
    rw [← hf]
    change _ = (wr C.gates _).getD C.output false
    rw [e, wr_low _ _ _ (by rw [ext_len]; omega), ext_lt]
  have fl : ∀ x : Fin 9 → Bool, ∀ k, k ≠ i → x k = flip i x k := by
    intro x k hk
    simp [flip, hk]
  have h9 : (bits n 0 || bits n 2) = (flip i (bits n) 0 || flip i (bits n) 2) := by
    rw [← fl _ 0 h0.symm, ← fl _ 2 h02.symm]
  have hji : (j : ℕ) ≠ (i : ℕ) := by
    intro e
    exact hij (Fin.ext (by simpa using e.symm))
  have hext := ext_eq (bits n) (flip i (bits n)) (fun k => k = i) h9
    (fun k hk => fl _ k (fun e => hk (by rw [e])))
  apply hne
  rw [← hf, ← hf]
  refine sim 10 _ _ (fun k => k = i) (fun k hk => by omega) (ext_len _) (ext_len _)
    hext C.gates ?_ _ hout
  intro g' hg' u v huv hu hv
  have hg2 : g' = g ∨ g' ∈ l1 ++ l2 := by
    rw [hs] at hg'
    rcases List.mem_append.1 hg' with q | q
    · exact Or.inr (List.mem_append_left _ q)
    · rcases List.mem_cons.1 q with q | q
      · exact Or.inl q
      · exact Or.inr (List.mem_append_right _ q)
  rcases hg2 with rfl | hg2
  · have huj : u j = c := by rw [hu _ (by omega), ext_w10, hj]
    have hvj : v j = c := by rw [← huv _ hji, huj]
    rcases hl with hl | hl
    · rw [hl]
      simp only [List.map_cons, List.map_nil]
      rw [huj, hvj]
      exact (hcv _ _).1
    · rw [hl]
      simp only [List.map_cons, List.map_nil]
      rw [huj, hvj]
      exact (hcv _ _).2
  · refine avoid g' (h2 g' hg').1 (h2 g' hg').2 u v fun k hk => huv k ?_
    rintro rfl
    exact hav g' hg2 hk

end PEqualNP.Outside.L_meta_3582

theorem PEqualNP.Outside.L_meta_3582 : have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => x1 (0 : Fin (9 : ℕ)) && x1 (1 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (2 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (3 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (4 : Fin (9 : ℕ)) || x1 (4 : Fin (9 : ℕ)) && x1 (0 : Fin (9 : ℕ)) || x1 (0 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (6 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (5 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (6 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (8 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x2 → (∀ (x4 : Fin (9 : ℕ) → Bool), x2.eval (List.ofFn x4 ++ [x4 (0 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ))]) = x1 x4) → ∀ (x5 : Fin (9 : ℕ)) (x6 : Fin (10 : ℕ)), x5 ≠ (0 : Fin (9 : ℕ)) → x5 ≠ (2 : Fin (9 : ℕ)) → x5.castSucc ≠ x6 → ∀ x10 ∈ x2.gates, x10.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x10.op = PEqualNP.CircuitLowerBounds.GateOp.or → x10.inputs = [↑x5, ↑x6] ∨ x10.inputs = [↑x6, ↑x5] → (2 : ℕ) ≤ (List.filter (fun (x14 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x14.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x14.inputs).contains ↑x5) x2.gates).length := by
  intro x1 C h2 hf i j h0 h02 hij g hg hop hl
  exact PEqualNP.Outside.L_meta_3582.main C h2 hf i j h0 h02 hij g hg hop hl
