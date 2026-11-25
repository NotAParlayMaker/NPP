import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_1593_3
    (hElimA : ∀ (n : ℕ) (f : (Fin n → Bool) → Bool) (a : Fin n) (s : ℕ),
      HasCircuitSize n f s →
      (∀ x : Fin n → Bool, x a = Bool.true → f x = Bool.true) →
      (∃ x y : Fin n → Bool,
        f (Function.update x a Bool.false) ≠ f (Function.update y a Bool.false)) →
      ∃ t : ℕ, t + 1 ≤ s ∧
        HasCircuitSize n (fun x : Fin n → Bool => f (Function.update x a Bool.false)) t)
    (hPureCubic : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (f : (Fin n → Bool) → Bool),
      (∀ v : Fin n, (G.neighborSet v).ncard = 3) →
      (∀ (w : Fin n) (c : G.Walk w w), c.IsCycle → 7 ≤ c.length) →
      (∃ i j : Fin n, G.Adj i j) →
      (∀ x : Fin n → Bool,
        f x = Bool.true ↔ ∃ i j : Fin n, G.Adj i j ∧ x i = Bool.true ∧ x j = Bool.true) →
      ∃ z : Fin n, ∀ s : ℕ,
        HasCircuitSize n f s →
        ∃ t : ℕ, t + 4 ≤ s ∧
          HasCircuitSize n (fun x : Fin n → Bool => f (Function.update x z Bool.false)) t) :
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n)), (∀ v : Fin n, v ∉ A → (G.neighborSet v).ncard = 3) → (∀ (w : Fin n) (c : G.Walk w w), c.IsCycle → 7 ≤ c.length) → (∀ i j : Fin n, G.Adj i j → i ∉ A) → (∃ i1 j1 : Fin n, G.Adj i1 j1) → ∃ z : Fin n, z ∉ A ∧ ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize n (fun x : Fin n → Bool => @decide ((∃ a ∈ A, x a = true) ∨ ∃ i2 j2 : Fin n, G.Adj i2 j2 ∧ x i2 = true ∧ x j2 = true) (Classical.propDecidable _)) s → ∃ t : ℕ, t + 4 ≤ s ∧ PEqualNP.MetaComplexity.HasCircuitSize n (fun x' : Fin n → Bool => @decide ((∃ a' ∈ A, x' a' = true) ∨ ∃ i3 j3 : Fin n, (G.deleteEdges (G.incidenceSet z)).Adj i3 j3 ∧ x' i3 = true ∧ x' j3 = true) (Classical.propDecidable _)) t := by
  classical
  let step : List Bool → Gate → List Bool :=
    fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have length_foldl : ∀ (gs : List Gate) (w : List Bool),
      (gs.foldl step w).length = w.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro w; simp
    | cons g gs ih =>
      intro w
      simp only [List.foldl_cons, ih, step, List.length_append, List.length_cons, List.length_nil]
      omega
  have getD_append_lt : ∀ (w t : List Bool) (i : ℕ), i < w.length →
      (w ++ t).getD i false = w.getD i false := by
    intro w t i hi
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
  have getD_foldl_lt : ∀ (gs : List Gate) (w : List Bool) (i : ℕ), i < w.length →
      (gs.foldl step w).getD i false = w.getD i false := by
    intro gs
    induction gs with
    | nil => intro w i _; rfl
    | cons g gs ih =>
      intro w i hi
      rw [List.foldl_cons, ih (step w g) i (by simp [step]; omega)]
      exact getD_append_lt w _ i hi
  have remap : ∀ (n₁ n₂ : ℕ) (C : Circuit) (fin : Fin n₁ → ℕ),
      FanInTwo C →
      (∀ i : Fin n₁, fin i < n₂ ∨ n₂ + C.gates.length ≤ fin i) →
      ∃ C' : Circuit, FanInTwo C' ∧ C'.size = C.size ∧
        ∀ (x₁ : Fin n₁ → Bool) (x₂ : Fin n₂ → Bool),
          (∀ i : Fin n₁, (if h : fin i < n₂ then x₂ ⟨fin i, h⟩ else false) = x₁ i) →
          C'.eval (List.ofFn x₂) = C.eval (List.ofFn x₁) := by
    intro n₁ n₂ C fin hF hbound
    let φ : ℕ → ℕ := fun w => if h : w < n₁ then fin ⟨w, h⟩ else n₂ + (w - n₁)
    let mapG : Gate → Gate := fun g => ⟨g.op, g.inputs.map φ⟩
    let C' : Circuit := ⟨C.gates.map mapG, φ C.output⟩
    refine ⟨C', ?_, ?_, ?_⟩
    · intro g' hg'
      obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hg'
      obtain ⟨hop, hlen⟩ := hF g hg
      exact ⟨hop, by simp [mapG, hlen]⟩
    · exact List.length_map ..
    · intro x₁ x₂ hagree
      have hmain : ∀ (gs : List Gate) (w₁ w₂ : List Bool),
          w₁.length ≥ n₁ →
          w₂.length ≥ n₂ →
          w₁.length - n₁ = w₂.length - n₂ →
          w₂.length + gs.length ≤ n₂ + C.gates.length →
          (∀ i : Fin n₁, w₁.getD i.val false = x₁ i) →
          (∀ j : Fin n₂, w₂.getD j.val false = x₂ j) →
          (∀ k : ℕ, k < w₁.length - n₁ → w₂.getD (n₂ + k) false = w₁.getD (n₁ + k) false) →
          let r₁ := gs.foldl step w₁
          let r₂ := (gs.map mapG).foldl step w₂
          r₁.length = w₁.length + gs.length ∧
          r₂.length = w₂.length + gs.length ∧
          (∀ k : ℕ, k < r₁.length - n₁ → r₂.getD (n₂ + k) false = r₁.getD (n₁ + k) false) := by
        intro gs
        induction gs with
        | nil =>
          intro w₁ w₂ _ _ _ _ _ _ hsame
          exact ⟨by simp, by simp, hsame⟩
        | cons g gs ih =>
          intro w₁ w₂ hw₁ hw₂ hdiff hle hx₁ hx₂ hsame
          have hwire : ∀ u : ℕ, w₂.getD (φ u) false = w₁.getD u false := by
            intro u
            by_cases hu : u < n₁
            · simp only [φ, hu, ↓reduceDIte]
              rw [hx₁ ⟨u, hu⟩, ← hagree ⟨u, hu⟩]
              rcases hbound ⟨u, hu⟩ with hlt | hge
              · simp only [hlt, ↓reduceDIte]
                exact hx₂ ⟨fin ⟨u, hu⟩, hlt⟩
              · have hnot : ¬ fin ⟨u, hu⟩ < n₂ := by omega
                simp only [hnot, ↓reduceDIte]
                have hoob : w₂.length ≤ fin ⟨u, hu⟩ := by
                  simp only [List.length_cons] at hle
                  omega
                simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hoob]
            · simp only [φ, hu, ↓reduceDIte]
              by_cases hk : u - n₁ < w₁.length - n₁
              · have h1 := hsame (u - n₁) hk
                have heq : n₁ + (u - n₁) = u := by omega
                rwa [heq] at h1
              · have hoob₁ : w₁.length ≤ u := by omega
                have hoob₂ : w₂.length ≤ n₂ + (u - n₁) := by omega
                simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hoob₁,
                  List.getElem?_eq_none hoob₂]
          have heval : (mapG g).op.eval ((mapG g).inputs.map fun i => w₂.getD i false) =
              g.op.eval (g.inputs.map fun i => w₁.getD i false) := by
            simp only [mapG, List.map_map]
            congr 1
            apply List.map_congr_left
            intro u _
            exact hwire u
          have hstep_same : ∀ k : ℕ, k < (step w₁ g).length - n₁ →
              (step w₂ (mapG g)).getD (n₂ + k) false = (step w₁ g).getD (n₁ + k) false := by
            intro k hk
            simp only [step, List.length_append, List.length_cons, List.length_nil] at hk
            by_cases hlt : k < w₁.length - n₁
            · rw [getD_append_lt w₂ _ (n₂ + k) (by omega),
                getD_append_lt w₁ _ (n₁ + k) (by omega)]
              exact hsame k hlt
            · have hk_eq : k = w₁.length - n₁ := by omega
              have hlen₁ : n₁ + k = w₁.length := by omega
              have hlen₂ : n₂ + k = w₂.length := by omega
              rw [hlen₁, hlen₂]
              have h1 : (step w₂ (mapG g)).getD w₂.length false =
                  (mapG g).op.eval ((mapG g).inputs.map fun i => w₂.getD i false) := by
                simp [step]
              have h2 : (step w₁ g).getD w₁.length false =
                  g.op.eval (g.inputs.map fun i => w₁.getD i false) := by
                simp [step]
              rw [h1, h2]
              exact heval
          have hrec := ih (step w₁ g) (step w₂ (mapG g))
            (by simp [step]; omega)
            (by simp [step]; omega)
            (by simp [step]; omega)
            (by simp [step] at hle ⊢; omega)
            (fun i => by rw [getD_append_lt w₁ _ i.val (by omega)]; exact hx₁ i)
            (fun j => by rw [getD_append_lt w₂ _ j.val (by omega)]; exact hx₂ j)
            hstep_same
          simp only [List.map_cons, List.foldl_cons]
          refine ⟨?_, ?_, hrec.2.2⟩
          · rw [hrec.1]; simp [step]; omega
          · rw [hrec.2.1]; simp [step]; omega
      have hres := hmain C.gates (List.ofFn x₁) (List.ofFn x₂)
        (by simp) (by simp) (by simp) (by simp)
        (fun i => by simp [List.getD_eq_getElem?_getD, i.isLt])
        (fun j => by simp [List.getD_eq_getElem?_getD, j.isLt])
        (fun k hk => by simp at hk)
      change (C'.gates.foldl step (List.ofFn x₂)).getD (φ C.output) false =
        (C.gates.foldl step (List.ofFn x₁)).getD C.output false
      by_cases hu : C.output < n₁
      · simp only [φ, hu, ↓reduceDIte]
        rw [getD_foldl_lt C.gates (List.ofFn x₁) C.output (by simp [hu])]
        have h1 : (List.ofFn x₁).getD C.output false = x₁ ⟨C.output, hu⟩ := by
          simp [List.getD_eq_getElem?_getD, hu]
        rw [h1, ← hagree ⟨C.output, hu⟩]
        rcases hbound ⟨C.output, hu⟩ with hlt | hge
        · simp only [hlt, ↓reduceDIte]
          rw [getD_foldl_lt C'.gates (List.ofFn x₂) (fin ⟨C.output, hu⟩) (by simp [hlt])]
          simp [List.getD_eq_getElem?_getD, hlt]
        · have hnot : ¬ fin ⟨C.output, hu⟩ < n₂ := by omega
          simp only [hnot, ↓reduceDIte]
          have hoob : (C'.gates.foldl step (List.ofFn x₂)).length ≤ fin ⟨C.output, hu⟩ := by
            rw [length_foldl]; simp [C']; omega
          simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hoob]
      · simp only [φ, hu, ↓reduceDIte]
        by_cases hk : C.output - n₁ < (C.gates.foldl step (List.ofFn x₁)).length - n₁
        · have h1 := hres.2.2 (C.output - n₁) hk
          have heq : n₁ + (C.output - n₁) = C.output := by omega
          rwa [heq] at h1
        · have hoob₁ : (C.gates.foldl step (List.ofFn x₁)).length ≤ C.output := by omega
          have hoob₂ : (C'.gates.foldl step (List.ofFn x₂)).length ≤ n₂ + (C.output - n₁) := by
            rw [hres.2.1]; rw [hres.1] at hoob₁; simp at hoob₁ ⊢; omega
          simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hoob₁,
            List.getElem?_eq_none hoob₂]
  have appendOrs : ∀ (n : ℕ) (l : List (Fin n)) (D : Circuit),
      FanInTwo D →
      ∃ D' : Circuit, FanInTwo D' ∧ D'.size = D.size + l.length ∧
        ∀ x : Fin n → Bool,
          D'.eval (List.ofFn x) = (D.eval (List.ofFn x) || decide (∃ a ∈ l, x a = true)) := by
    intro n l
    induction l with
    | nil =>
      intro D hD
      exact ⟨D, hD, by simp, fun x => by simp⟩
    | cons a l ih =>
      intro D hD
      let gNew : Gate := ⟨GateOp.or, [D.output, a.val]⟩
      let D₁ : Circuit := ⟨D.gates ++ [gNew], n + D.gates.length⟩
      have hD₁ : FanInTwo D₁ := by
        intro g hg
        rcases List.mem_append.mp hg with hmem | hmem
        · exact hD g hmem
        · simp only [List.mem_singleton] at hmem
          subst hmem
          exact ⟨by simp [gNew], by simp [gNew]⟩
      have hD₁_eval : ∀ x : Fin n → Bool,
          D₁.eval (List.ofFn x) = (D.eval (List.ofFn x) || x a) := by
        intro x
        change ((D.gates ++ [gNew]).foldl step (List.ofFn x)).getD (n + D.gates.length) false = _
        rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
        set w := D.gates.foldl step (List.ofFn x)
        have hwlen : w.length = n + D.gates.length := by
          rw [length_foldl, List.length_ofFn]
        have hstep_eq : (step w gNew).getD (n + D.gates.length) false =
            gNew.op.eval (gNew.inputs.map fun i => w.getD i false) := by
          simp only [step, ← hwlen, List.getD_eq_getElem?_getD]
          simp
        rw [hstep_eq]
        have hxa : w.getD a.val false = x a := by
          rw [getD_foldl_lt D.gates (List.ofFn x) a.val (by simp [a.isLt])]
          simp [List.getD_eq_getElem?_getD, a.isLt]
        change (w.getD D.output false || (w.getD a.val false || false)) =
          (w.getD D.output false || x a)
        rw [hxa]
        simp
      obtain ⟨D', hD'F, hD'sz, hD'ev⟩ := ih D₁ hD₁
      refine ⟨D', hD'F, ?_, ?_⟩
      · rw [hD'sz]
        change (D.gates ++ [gNew]).length + l.length = D.gates.length + (l.length + 1)
        simp
        omega
      · intro x
        rw [hD'ev x, hD₁_eval x]
        by_cases h1 : D.eval (List.ofFn x) = true <;>
          by_cases h2 : x a = true <;>
          by_cases h3 : ∃ b ∈ l, x b = true <;>
          simp_all
  intro n G A hdeg hgirth hA hedge
  let S : Type := {v : Fin n // v ∉ A}
  let m : ℕ := Fintype.card S
  let e : Fin m ≃ S := (Fintype.equivFin S).symm
  let G' : SimpleGraph (Fin m) := SimpleGraph.comap (fun u : Fin m => (e u).1) G
  have hG'deg : ∀ u : Fin m, (G'.neighborSet u).ncard = 3 := by
    intro u
    have himg : (fun v : Fin m => (e v).1) '' G'.neighborSet u = G.neighborSet (e u).1 := by
      ext y
      constructor
      · rintro ⟨v, hv, rfl⟩
        exact hv
      · intro hy
        have hyA : y ∉ A := hA y (e u).1 hy.symm
        refine ⟨e.symm ⟨y, hyA⟩, ?_, by simp⟩
        change G.Adj (e u).1 (e (e.symm ⟨y, hyA⟩)).1
        simpa using hy
    have hinj : Function.Injective (fun v : Fin m => (e v).1) :=
      Subtype.val_injective.comp e.injective
    rw [← hdeg (e u).1 (e u).2, ← himg, Set.ncard_image_of_injective _ hinj]
  have hG'girth : ∀ (w : Fin m) (c : G'.Walk w w), c.IsCycle → 7 ≤ c.length := by
    intro w c hc
    let hom : G' →g G :=
      { toFun := fun u => (e u).1
        map_rel' := fun h => h }
    have hinj : Function.Injective hom := Subtype.val_injective.comp e.injective
    have hc' : (c.map hom).IsCycle := hc.map hinj
    have hlen := hgirth (hom w) (c.map hom) hc'
    simpa [SimpleGraph.Walk.length_map] using hlen
  have hG'edge : ∃ i j : Fin m, G'.Adj i j := by
    obtain ⟨i1, j1, hij⟩ := hedge
    have hi1 : i1 ∉ A := hA i1 j1 hij
    have hj1 : j1 ∉ A := hA j1 i1 hij.symm
    refine ⟨e.symm ⟨i1, hi1⟩, e.symm ⟨j1, hj1⟩, ?_⟩
    change G.Adj (e (e.symm ⟨i1, hi1⟩)).1 (e (e.symm ⟨j1, hj1⟩)).1
    simpa using hij
  let fG' : (Fin m → Bool) → Bool := fun y =>
    @decide (∃ i j : Fin m, G'.Adj i j ∧ y i = true ∧ y j = true) (Classical.propDecidable _)
  have hfG' : ∀ y : Fin m → Bool,
      fG' y = true ↔ ∃ i j : Fin m, G'.Adj i j ∧ y i = true ∧ y j = true := by
    intro y
    simp only [fG', decide_eq_true_eq]
  obtain ⟨z', hz'⟩ := hPureCubic m G' fG' hG'deg hG'girth hG'edge hfG'
  refine ⟨(e z').1, (e z').2, ?_⟩
  intro s hs
  have elimB : ∀ B : Finset (Fin n), B ⊆ A → ∀ s₁ : ℕ,
      HasCircuitSize n
        (fun x : Fin n → Bool =>
          @decide ((∃ a ∈ B, x a = true) ∨ ∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)
            (Classical.propDecidable _)) s₁ →
      ∃ s₀ : ℕ, s₀ + B.card ≤ s₁ ∧
        HasCircuitSize n
          (fun x : Fin n → Bool =>
            @decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)
              (Classical.propDecidable _)) s₀ := by
    intro B
    induction B using Finset.induction_on with
    | empty =>
      intro _ s₁ hs₁
      refine ⟨s₁, by simp, ?_⟩
      convert hs₁ using 1
      funext x
      simp
    | @insert a B' haB' ih =>
      intro hsub s₁ hs₁
      have haA : a ∈ A := hsub (Finset.mem_insert_self a B')
      have hsub' : B' ⊆ A := (Finset.subset_insert a B').trans hsub
      let fB : (Fin n → Bool) → Bool := fun x =>
        @decide ((∃ b ∈ insert a B', x b = true) ∨
          ∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true) (Classical.propDecidable _)
      have htrue : ∀ x : Fin n → Bool, x a = true → fB x = true := by
        intro x hxa
        simp only [fB, decide_eq_true_eq]
        exact Or.inl ⟨a, Finset.mem_insert_self a B', hxa⟩
      have hnc : ∃ x y : Fin n → Bool,
          fB (Function.update x a false) ≠ fB (Function.update y a false) := by
        refine ⟨fun _ => false, fun _ => true, ?_⟩
        have h0 : fB (Function.update (fun _ => false) a false) = false := by
          simp only [fB, decide_eq_false_iff_not]
          rintro (⟨b, _, hb⟩ | ⟨i, _, _, hi, _⟩)
          · simp [Function.update] at hb
          · simp [Function.update] at hi
        obtain ⟨i1, j1, hij⟩ := hedge
        have hi1 : i1 ≠ a := fun h => hA i1 j1 hij (h ▸ haA)
        have hj1 : j1 ≠ a := fun h => hA j1 i1 hij.symm (h ▸ haA)
        have h1 : fB (Function.update (fun _ => true) a false) = true := by
          simp only [fB, decide_eq_true_eq]
          exact Or.inr ⟨i1, j1, hij, by simp [Function.update_of_ne hi1],
            by simp [Function.update_of_ne hj1]⟩
        rw [h0, h1]
        decide
      obtain ⟨s₂, hs₂le, hs₂⟩ := hElimA n fB a s₁ hs₁ htrue hnc
      have hfeq : (fun x : Fin n → Bool => fB (Function.update x a false)) =
          (fun x : Fin n → Bool =>
            @decide ((∃ b ∈ B', x b = true) ∨
              ∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)
              (Classical.propDecidable _)) := by
        funext x
        apply Bool.eq_iff_iff.mpr
        simp only [fB, decide_eq_true_eq]
        constructor
        · rintro (⟨b, hb, hxb⟩ | ⟨i, j, hij, hi, hj⟩)
          · rcases Finset.mem_insert.mp hb with rfl | hb'
            · simp at hxb
            · have hba : b ≠ a := fun h => haB' (h ▸ hb')
              exact Or.inl ⟨b, hb', by simpa [Function.update_of_ne hba] using hxb⟩
          · have hia : i ≠ a := fun h => hA i j hij (h ▸ haA)
            have hja : j ≠ a := fun h => hA j i hij.symm (h ▸ haA)
            exact Or.inr ⟨i, j, hij, by simpa [Function.update_of_ne hia] using hi,
              by simpa [Function.update_of_ne hja] using hj⟩
        · rintro (⟨b, hb', hxb⟩ | ⟨i, j, hij, hi, hj⟩)
          · have hba : b ≠ a := fun h => haB' (h ▸ hb')
            exact Or.inl ⟨b, Finset.mem_insert_of_mem hb',
              by simpa [Function.update_of_ne hba] using hxb⟩
          · have hia : i ≠ a := fun h => hA i j hij (h ▸ haA)
            have hja : j ≠ a := fun h => hA j i hij.symm (h ▸ haA)
            exact Or.inr ⟨i, j, hij, by simpa [Function.update_of_ne hia] using hi,
              by simpa [Function.update_of_ne hja] using hj⟩
      rw [hfeq] at hs₂
      obtain ⟨s₀, hs₀le, hs₀⟩ := ih hsub' s₂ hs₂
      refine ⟨s₀, ?_, hs₀⟩
      rw [Finset.card_insert_of_notMem haB']
      omega
  obtain ⟨s₀, hs₀le, C₀, hC₀F, hC₀sz, hC₀ev⟩ := elimB A (Finset.Subset.refl A) s hs
  let fin₁ : Fin n → ℕ := fun i =>
    if hi : i ∈ A then m + C₀.gates.length else (e.symm ⟨i, hi⟩).val
  have hfin₁ : ∀ i : Fin n, fin₁ i < m ∨ m + C₀.gates.length ≤ fin₁ i := by
    intro i
    by_cases hi : i ∈ A
    · right; simp [fin₁, hi]
    · left; simp [fin₁, hi, (e.symm ⟨i, hi⟩).isLt]
  obtain ⟨C₀', hC₀'F, hC₀'sz, hC₀'ev⟩ := remap n m C₀ fin₁ hC₀F hfin₁
  have hs₀' : HasCircuitSize m
      (fun y : Fin m → Bool =>
        @decide (∃ i j : Fin m, G'.Adj i j ∧ y i = true ∧ y j = true)
          (Classical.propDecidable _)) s₀ := by
    refine ⟨C₀', hC₀'F, by omega, ?_⟩
    intro y
    let x₁ : Fin n → Bool := fun i => if hi : i ∈ A then false else y (e.symm ⟨i, hi⟩)
    have hagree : ∀ i : Fin n, (if h : fin₁ i < m then y ⟨fin₁ i, h⟩ else false) = x₁ i := by
      intro i
      by_cases hi : i ∈ A
      · have hnot : ¬ fin₁ i < m := by simp [fin₁, hi]
        simp [x₁, hi, hnot]
      · simp [fin₁, x₁, hi]
    rw [hC₀'ev x₁ y hagree, hC₀ev x₁]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    constructor
    · rintro ⟨i, j, hij, hi, hj⟩
      have hiA : i ∉ A := hA i j hij
      have hjA : j ∉ A := hA j i hij.symm
      refine ⟨e.symm ⟨i, hiA⟩, e.symm ⟨j, hjA⟩, ?_, ?_, ?_⟩
      · change G.Adj (e (e.symm ⟨i, hiA⟩)).1 (e (e.symm ⟨j, hjA⟩)).1
        simpa using hij
      · simpa [x₁, hiA] using hi
      · simpa [x₁, hjA] using hj
    · rintro ⟨u, v, huv, hu, hv⟩
      refine ⟨(e u).1, (e v).1, huv, ?_, ?_⟩
      · simp [x₁, (e u).2, hu]
      · simp [x₁, (e v).2, hv]
  obtain ⟨t₀, ht₀le, D₀, hD₀F, hD₀sz, hD₀ev⟩ := hz' s₀ hs₀'
  let fin₂ : Fin m → ℕ := fun u => (e u).1.val
  have hfin₂ : ∀ u : Fin m, fin₂ u < n ∨ n + D₀.gates.length ≤ fin₂ u :=
    fun u => Or.inl (e u).1.isLt
  obtain ⟨D₀', hD₀'F, hD₀'sz, hD₀'ev⟩ := remap m n D₀ fin₂ hD₀F hfin₂
  have hD₀'eval : ∀ x : Fin n → Bool,
      D₀'.eval (List.ofFn x) =
        @decide (∃ i j : Fin n, (G.deleteEdges (G.incidenceSet (e z').1)).Adj i j ∧
          x i = true ∧ x j = true) (Classical.propDecidable _) := by
    intro x
    let y : Fin m → Bool := fun u => x (e u).1
    have hagree : ∀ u : Fin m, (if h : fin₂ u < n then x ⟨fin₂ u, h⟩ else false) = y u := by
      intro u
      simp [fin₂, y]
    rw [hD₀'ev y x hagree, hD₀ev y]
    have del_adj : ∀ {α : Type} (H : SimpleGraph α) (z u v : α),
        (H.deleteEdges (H.incidenceSet z)).Adj u v ↔ H.Adj u v ∧ u ≠ z ∧ v ≠ z :=
      fun H z u v => SimpleGraph.deleteIncidenceSet_adj
    apply Bool.eq_iff_iff.mpr
    rw [hfG']
    simp only [decide_eq_true_eq, del_adj]
    constructor
    · rintro ⟨u, v, huv, hu, hv⟩
      have huz : u ≠ z' := by intro heq; simp [heq] at hu
      have hvz : v ≠ z' := by intro heq; simp [heq] at hv
      have hu' : x (e u).1 = true := by simpa [y, Function.update_of_ne huz] using hu
      have hv' : x (e v).1 = true := by simpa [y, Function.update_of_ne hvz] using hv
      refine ⟨(e u).1, (e v).1, ⟨huv, ?_, ?_⟩, hu', hv'⟩
      · intro heq; exact huz (e.injective (Subtype.ext heq))
      · intro heq; exact hvz (e.injective (Subtype.ext heq))
    · rintro ⟨i, j, ⟨hij, hiz, hjz⟩, hi, hj⟩
      have hiA : i ∉ A := hA i j hij
      have hjA : j ∉ A := hA j i hij.symm
      have huz : e.symm ⟨i, hiA⟩ ≠ z' := by
        intro heq
        have h1 := congrArg (fun t => (e t).1) heq
        simp at h1
        exact hiz h1
      have hvz : e.symm ⟨j, hjA⟩ ≠ z' := by
        intro heq
        have h1 := congrArg (fun t => (e t).1) heq
        simp at h1
        exact hjz h1
      refine ⟨e.symm ⟨i, hiA⟩, e.symm ⟨j, hjA⟩, ?_, ?_, ?_⟩
      · change G.Adj (e (e.symm ⟨i, hiA⟩)).1 (e (e.symm ⟨j, hjA⟩)).1
        simpa using hij
      · simpa [y, Function.update_of_ne huz] using hi
      · simpa [y, Function.update_of_ne hvz] using hj
  obtain ⟨D, hDF, hDsz, hDev⟩ := appendOrs n A.toList D₀' hD₀'F
  refine ⟨t₀ + A.card, by omega, D, hDF, ?_, ?_⟩
  · rw [hDsz, hD₀'sz, Finset.length_toList]
    omega
  · intro x
    rw [hDev x, hD₀'eval x]
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    constructor
    · rintro (h | ⟨a, ha, hxa⟩)
      · exact Or.inr h
      · exact Or.inl ⟨a, Finset.mem_toList.mp ha, hxa⟩
    · rintro (⟨a, ha, hxa⟩ | h)
      · exact Or.inr ⟨a, Finset.mem_toList.mpr ha, hxa⟩
      · exact Or.inl h
