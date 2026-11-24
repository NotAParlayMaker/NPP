import Mathlib.Data.List.GetD
import PEqualNP.Defs

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 10000 in
theorem PEqualNP.Outside.R_meta_3590_47
    (h1 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : Fin (10 : ℕ)), (10 : ℕ) * ↑x2 + ↑x3 ∈ [(1 : ℕ), (2 : ℕ), (3 : ℕ), (6 : ℕ), (12 : ℕ), (13 : ℕ)] → PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x8 : Fin (9 : ℕ) → Bool), have x9 : List Bool := List.ofFn x8 ++ [x8 (0 : Fin (9 : ℕ)) || x8 (4 : Fin (9 : ℕ))]; x1.eval (x9 ++ [x9.getD (↑x2) Bool.false || x9.getD (↑x3) Bool.false]) = (fun (x10 : Fin (9 : ℕ) → Bool) => [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x11 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x10 x11.1 && x10 x11.2) x8) → (14 : ℕ) ≤ x1.size)
    (h2 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : Fin (10 : ℕ)), (10 : ℕ) * ↑x2 + ↑x3 ∈ [(14 : ℕ), (15 : ℕ), (16 : ℕ), (17 : ℕ), (18 : ℕ), (19 : ℕ)] → PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x8 : Fin (9 : ℕ) → Bool), have x9 : List Bool := List.ofFn x8 ++ [x8 (0 : Fin (9 : ℕ)) || x8 (4 : Fin (9 : ℕ))]; x1.eval (x9 ++ [x9.getD (↑x2) Bool.false || x9.getD (↑x3) Bool.false]) = (fun (x10 : Fin (9 : ℕ) → Bool) => [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x11 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x10 x11.1 && x10 x11.2) x8) → (14 : ℕ) ≤ x1.size)
    (h3 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : Fin (10 : ℕ)), (10 : ℕ) * ↑x2 + ↑x3 ∈ [(23 : ℕ), (24 : ℕ), (26 : ℕ), (27 : ℕ), (28 : ℕ), (29 : ℕ)] → PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x8 : Fin (9 : ℕ) → Bool), have x9 : List Bool := List.ofFn x8 ++ [x8 (0 : Fin (9 : ℕ)) || x8 (4 : Fin (9 : ℕ))]; x1.eval (x9 ++ [x9.getD (↑x2) Bool.false || x9.getD (↑x3) Bool.false]) = (fun (x10 : Fin (9 : ℕ) → Bool) => [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x11 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x10 x11.1 && x10 x11.2) x8) → (14 : ℕ) ≤ x1.size)
    (h4 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : Fin (10 : ℕ)), (10 : ℕ) * ↑x2 + ↑x3 ∈ [(34 : ℕ), (36 : ℕ), (39 : ℕ), (46 : ℕ), (67 : ℕ), (69 : ℕ)] → PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x8 : Fin (9 : ℕ) → Bool), have x9 : List Bool := List.ofFn x8 ++ [x8 (0 : Fin (9 : ℕ)) || x8 (4 : Fin (9 : ℕ))]; x1.eval (x9 ++ [x9.getD (↑x2) Bool.false || x9.getD (↑x3) Bool.false]) = (fun (x10 : Fin (9 : ℕ) → Bool) => [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x11 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x10 x11.1 && x10 x11.2) x8) → (14 : ℕ) ≤ x1.size) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : Fin (10 : ℕ)),   PEqualNP.MetaComplexity.FanInTwo x1 →     x2 < x3 →       ¬(x2 = (0 : Fin (10 : ℕ)) ∧ x3 = (4 : Fin (10 : ℕ))) →         ¬((x2 = (0 : Fin (10 : ℕ)) ∨ x2 = (4 : Fin (10 : ℕ))) ∧ x3 = (9 : Fin (10 : ℕ))) →           (∀ (x8 : Fin (9 : ℕ) → Bool),               have x9 : List Bool := List.ofFn x8 ++ [x8 (0 : Fin (9 : ℕ)) || x8 (4 : Fin (9 : ℕ))];               x1.eval (x9 ++ [x9.getD (↑x2) Bool.false || x9.getD (↑x3) Bool.false]) = (fun (x10 : Fin (9 : ℕ) → Bool) => [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x11 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x10 x11.1 && x10 x11.2) x8) →             (14 : ℕ) ≤ x1.size := by
  intro C x2 x3 hfan hlt h04 h049 heval
  let es : List (Fin 9 × Fin 9) :=
    [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8), (5, 7), (6, 8), (8, 5)]
  let edgeF (x : Fin 9 → Bool) : Bool := es.any fun e => x e.1 && x e.2
  let feed (x : Fin 9 → Bool) : List Bool := List.ofFn x ++ [x 0 || x 4]
  let reps : List ℕ :=
    [1, 2, 3, 6, 12, 13, 14, 15, 16, 17, 18, 19, 23, 24, 26, 27, 28, 29, 34, 36, 39, 46, 67, 69]
  have core : ∀ (D : PEqualNP.CircuitLowerBounds.Circuit) (u v : Fin 10),
      10 * u.val + v.val ∈ reps →
      PEqualNP.MetaComplexity.FanInTwo D →
      (∀ x : Fin 9 → Bool,
        D.eval (feed x ++ [(feed x).getD u.val false || (feed x).getD v.val false]) = edgeF x) →
      14 ≤ D.size := fun D u v hmem =>
    (@List.mem_append ℕ (10 * u.val + v.val)
      [1, 2, 3, 6, 12, 13]
      ([14, 15, 16, 17, 18, 19] ++ ([23, 24, 26, 27, 28, 29] ++ [34, 36, 39, 46, 67, 69]))).mp hmem |>.elim
      (h1 D u v) fun hmem =>
    (@List.mem_append ℕ (10 * u.val + v.val)
      [14, 15, 16, 17, 18, 19]
      ([23, 24, 26, 27, 28, 29] ++ [34, 36, 39, 46, 67, 69])).mp hmem |>.elim
      (h2 D u v) fun hmem =>
    (@List.mem_append ℕ (10 * u.val + v.val)
      [23, 24, 26, 27, 28, 29]
      [34, 36, 39, 46, 67, 69]).mp hmem |>.elim
      (h3 D u v) (h4 D u v)
  let ρ (i : ℕ) : ℕ := ([0, 5, 8, 3, 4, 1, 7, 6, 2] : List ℕ).getD i i
  have hρ_lt9 : ∀ i : Fin 9, ρ i.val < 9 := by decide
  have hρ_lt10 : ∀ i : Fin 10, ρ i.val < 10 := by decide
  have hρ_fix : ∀ i : ℕ, 9 ≤ i → ρ i = i := fun i hi =>
    List.getD_eq_default [0, 5, 8, 3, 4, 1, 7, 6, 2] i hi
  let σ (i : Fin 9) : Fin 9 := ⟨ρ i.val, hρ_lt9 i⟩
  let τ (i : Fin 10) : Fin 10 := ⟨ρ i.val, hρ_lt10 i⟩
  have horbit : ∀ u v : Fin 10,
      u < v →
      ¬(u = 0 ∧ v = 4) →
      ¬((u = 0 ∨ u = 4) ∧ v = 9) →
      10 * u.val + v.val ∈ reps ∨
        10 * min (ρ u.val) (ρ v.val) + max (ρ u.val) (ρ v.val) ∈ reps := by
    dsimp only [reps, ρ]
    decide
  apply (horbit x2 x3 hlt h04 h049).elim
  · intro hrep
    exact core C x2 x3 hrep hfan heval
  · intro hrep
    let u : Fin 10 := min (τ x2) (τ x3)
    let v : Fin 10 := max (τ x2) (τ x3)
    have hu_val : u.val = min (ρ x2.val) (ρ x3.val) :=
      (le_total (τ x2) (τ x3)).elim
        (fun hle => by dsimp only [u]; rw [min_eq_left hle, Nat.min_eq_left hle])
        (fun hge => by dsimp only [u]; rw [min_eq_right hge, Nat.min_eq_right hge])
    have hv_val : v.val = max (ρ x2.val) (ρ x3.val) :=
      (le_total (τ x2) (τ x3)).elim
        (fun hle => by dsimp only [v]; rw [max_eq_right hle, Nat.max_eq_right hle])
        (fun hge => by dsimp only [v]; rw [max_eq_left hge, Nat.max_eq_left hge])
    have hrep' : 10 * u.val + v.val ∈ reps := by rwa [hu_val, hv_val]
    let renameGate (g : PEqualNP.CircuitLowerBounds.Gate) : PEqualNP.CircuitLowerBounds.Gate :=
      ⟨g.op, g.inputs.map ρ⟩
    let D : PEqualNP.CircuitLowerBounds.Circuit := ⟨C.gates.map renameGate, ρ C.output⟩
    have hfanD : PEqualNP.MetaComplexity.FanInTwo D := by
      intro g hg
      exact (List.mem_map.mp hg).elim fun g' hg' =>
        hg'.2 ▸ ⟨(hfan g' hg'.1).1, by simpa only [renameGate, List.length_map] using (hfan g' hg'.1).2⟩
    have hsizeD : D.size = C.size := by
      change (C.gates.map renameGate).length = C.gates.length
      exact List.length_map _
    have hF0 : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 : Bool,
        ((b0 && b5) || ((b5 && b8) || ((b8 && b3) || ((b3 && b4) || ((b4 && b0) || ((b0 && b1) ||
          ((b5 && b7) || ((b8 && b6) || ((b3 && b2) || ((b1 && b6) || ((b7 && b2) || ((b2 && b1) || false)))))))))))) =
        ((b0 && b1) || ((b1 && b2) || ((b2 && b3) || ((b3 && b4) || ((b4 && b0) || ((b0 && b5) ||
          ((b1 && b6) || ((b2 && b7) || ((b3 && b8) || ((b5 && b7) || ((b6 && b8) || ((b8 && b5) || false)))))))))))) := by
      decide
    have hsym (x : Fin 9 → Bool) : edgeF (x ∘ σ) = edgeF x :=
      hF0 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7) (x 8)
    let step (w : List Bool) (g : PEqualNP.CircuitLowerBounds.Gate) : List Bool :=
      w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
    have hlast (w : List Bool) (a : Bool) : (w ++ [a]).getD w.length false = a := by
      rw [List.getD_append_right _ _ _ _ (le_refl _), Nat.sub_self]
      rfl
    have hold (w : List Bool) (a : Bool) (i : ℕ) (hne : i ≠ w.length) :
        (w ++ [a]).getD i false = w.getD i false := by
      by_cases hi : i < w.length
      · exact List.getD_append _ _ _ _ hi
      · rw [List.getD_eq_default _ _ (by rw [List.length_append, List.length_singleton]; omega),
            List.getD_eq_default _ _ (by omega)]
    have simulate (gs : List PEqualNP.CircuitLowerBounds.Gate) (w z : List Bool)
        (hlen : w.length = z.length) (h9 : 9 ≤ w.length)
        (heq : ∀ i, w.getD i false = z.getD (ρ i) false) :
        ∀ i, (gs.foldl step w).getD i false =
          ((gs.map renameGate).foldl step z).getD (ρ i) false := by
      induction gs generalizing w z with
      | nil => exact heq
      | cons g gs ih =>
        simp only [List.map_cons, List.foldl_cons]
        apply ih
        · simp only [step, List.length_append, List.length_singleton, hlen]
        · rw [show (step w g).length = w.length + 1 from by simp [step]]
          omega
        · intro i
          have hpins : g.inputs.map (fun j => w.getD j false) =
              (g.inputs.map ρ).map (fun j => z.getD j false) := by
            rw [List.map_map]
            exact List.map_congr_left fun j _ => heq j
          by_cases hi : i = w.length
          · rw [hi, hρ_fix _ h9]
            dsimp only [step, renameGate]
            rw [hlast]
            conv_rhs => rw [hlen]
            rw [hlast, hpins]
          · have hj : ρ i ≠ z.length := by
              by_cases hlt9 : i < 9
              · have hltρ : ρ i < 9 := hρ_lt9 ⟨i, hlt9⟩
                omega
              · rw [hρ_fix i (by omega)]
                omega
            dsimp only [step, renameGate]
            rw [hold _ _ _ hi, hold _ _ _ hj, heq]
    have feed_len (y : Fin 9 → Bool) : (feed y).length = 10 := by
      simp [feed]
    have feed_rel (x : Fin 9 → Bool) (j : Fin 10) :
        (feed (x ∘ σ)).getD j.val false = (feed x).getD (τ j).val false := by
      by_cases hj : j.val < 9
      · have hr : (τ j).val < 9 := hρ_lt9 ⟨j.val, hj⟩
        unfold feed
        rw [List.getD_append _ _ _ _ (by simpa only [List.length_ofFn] using hj),
            List.getD_append _ _ _ _ (by simpa only [List.length_ofFn] using hr),
            List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using hj),
            List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using hr),
            List.getElem_ofFn, List.getElem_ofFn]
        rfl
      · have hj9 : j.val = 9 := by have := j.isLt; omega
        have ht9 : (τ j).val = 9 := by change ρ j.val = 9; rw [hj9]; rfl
        rw [hj9, ht9]
        unfold feed
        rw [List.getD_append_right _ _ _ _ (by simp),
            List.getD_append_right _ _ _ _ (by simp),
            List.length_ofFn, List.length_ofFn]
        rfl
    rw [← hsizeD]
    apply core D u v hrep' hfanD
    intro x
    have hor_eq : ((feed (x ∘ σ)).getD x2.val false || (feed (x ∘ σ)).getD x3.val false) =
        ((feed x).getD u.val false || (feed x).getD v.val false) := by
      rw [feed_rel x x2, feed_rel x x3]
      exact (le_total (τ x2) (τ x3)).elim
        (fun hle => by dsimp only [u, v]; rw [min_eq_left hle, max_eq_right hle])
        (fun hge => by dsimp only [u, v]; rw [min_eq_right hge, max_eq_left hge, Bool.or_comm])
    let w := feed (x ∘ σ) ++ [(feed (x ∘ σ)).getD x2.val false || (feed (x ∘ σ)).getD x3.val false]
    let z := feed x ++ [(feed x).getD u.val false || (feed x).getD v.val false]
    have hsim := simulate C.gates w z
      (by simp [w, z, feed_len])
      (by simp [w, feed_len])
      (fun i => by
        by_cases hi10 : i < 10
        · have hr10 : ρ i < 10 := hρ_lt10 ⟨i, hi10⟩
          dsimp only [w, z]
          rw [hold (feed (x ∘ σ)) _ i (by rw [feed_len]; omega),
              hold (feed x) _ (ρ i) (by rw [feed_len]; omega)]
          exact feed_rel x ⟨i, hi10⟩
        · rw [hρ_fix i (by omega)]
          by_cases heq10 : i = 10
          · dsimp only [w, z]
            have hw10 : i = (feed (x ∘ σ)).length := by rw [feed_len]; exact heq10
            have hz10 : i = (feed x).length := by rw [feed_len]; exact heq10
            conv_lhs => rw [hw10]
            conv_rhs => rw [hz10]
            rw [hlast, hlast]
            exact hor_eq
          · rw [List.getD_eq_default _ _ (by simp [w, feed_len]; omega),
                List.getD_eq_default _ _ (by simp [z, feed_len]; omega)])
      C.output
    have hevC : C.eval w = D.eval z := hsim
    rw [← hevC]
    exact (heval (x ∘ σ)).trans (hsym x)
