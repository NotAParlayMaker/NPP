import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Relabel a minimum circuit so that its first gate uses one of the fixed pairs.
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.R_meta_1477_1
    (normalize :
      let E : List (ℕ × ℕ) := (List.range 21).flatMap fun p =>
      ((List.range 21).filter fun w =>
        decide ((w + 21 - p) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ))).map fun w => (p, 21 + w)
      let computes := fun C : Circuit => ∀ x : Fin 42 → Bool,
      C.eval (List.ofFn x) = true ↔
        ∃ u v : Fin 42, (u.val, v.val) ∈ E ∧ x u = true ∧ x v = true
      ∀ C : Circuit, Monotone2 C → computes C →
        ∃ (F : Circuit) (u v : Fin 42) (op : GateOp),
          Monotone2 F ∧ F.size ≤ C.size ∧ computes F ∧ u ≠ v ∧
          F.gates.head? = some ⟨op, [u.val, v.val]⟩ ∧
          (op = .or ∨ op = .and ∧ ((u.val, v.val) ∈ E ∨ (v.val, u.val) ∈ E)))
    (noSame :
      let E : List (ℕ × ℕ) := (List.range 21).flatMap fun p =>
      ((List.range 21).filter fun w =>
        decide ((w + 21 - p) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ))).map fun w => (p, 21 + w)
      let computes := fun C : Circuit => ∀ x : Fin 42 → Bool,
      C.eval (List.ofFn x) = true ↔
        ∃ u v : Fin 42, (u.val, v.val) ∈ E ∧ x u = true ∧ x v = true
      ¬ (∃ C : Circuit, Monotone2 C ∧ C.size ≤ 124 ∧ computes C ∧
        C.gates.head? = some ⟨GateOp.or, [0, 1]⟩ ∧ ∀ D : Circuit, Monotone2 D → computes D → C.size ≤ D.size))
    (noCross :
      let E : List (ℕ × ℕ) := (List.range 21).flatMap fun p =>
      ((List.range 21).filter fun w =>
        decide ((w + 21 - p) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ))).map fun w => (p, 21 + w)
      let computes := fun C : Circuit => ∀ x : Fin 42 → Bool,
      C.eval (List.ofFn x) = true ↔
        ∃ u v : Fin 42, (u.val, v.val) ∈ E ∧ x u = true ∧ x v = true
      ¬ (∃ C : Circuit, Monotone2 C ∧ C.size ≤ 124 ∧ computes C ∧
        (C.gates.head? = some ⟨GateOp.or, [0, 21]⟩ ∨
         C.gates.head? = some ⟨GateOp.or, [0, 22]⟩) ∧ ∀ D : Circuit, Monotone2 D → computes D → C.size ≤ D.size))
    (noAnd :
      let E : List (ℕ × ℕ) := (List.range 21).flatMap fun p =>
      ((List.range 21).filter fun w =>
        decide ((w + 21 - p) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ))).map fun w => (p, 21 + w)
      let computes := fun C : Circuit => ∀ x : Fin 42 → Bool,
      C.eval (List.ofFn x) = true ↔
        ∃ u v : Fin 42, (u.val, v.val) ∈ E ∧ x u = true ∧ x v = true
      ¬ (∃ C : Circuit, Monotone2 C ∧ C.size ≤ 124 ∧ computes C ∧
        C.gates.head? = some ⟨GateOp.and, [0, 21]⟩ ∧ ∀ D : Circuit, Monotone2 D → computes D → C.size ≤ D.size)) :
    ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 124 ∧ (∀ x : Fin 42 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 42, (u.val, v.val) ∈ ([(0, 21), (0, 26), (0, 28), (0, 38), (0, 41), (1, 21), (1, 22), (1, 27), (1, 29), (1, 39), (2, 22), (2, 23), (2, 28), (2, 30), (2, 40), (3, 23), (3, 24), (3, 29), (3, 31), (3, 41), (4, 21), (4, 24), (4, 25), (4, 30), (4, 32), (5, 22), (5, 25), (5, 26), (5, 31), (5, 33), (6, 23), (6, 26), (6, 27), (6, 32), (6, 34), (7, 24), (7, 27), (7, 28), (7, 33), (7, 35), (8, 25), (8, 28), (8, 29), (8, 34), (8, 36), (9, 26), (9, 29), (9, 30), (9, 35), (9, 37), (10, 27), (10, 30), (10, 31), (10, 36), (10, 38), (11, 28), (11, 31), (11, 32), (11, 37), (11, 39), (12, 29), (12, 32), (12, 33), (12, 38), (12, 40), (13, 30), (13, 33), (13, 34), (13, 39), (13, 41), (14, 21), (14, 31), (14, 34), (14, 35), (14, 40), (15, 22), (15, 32), (15, 35), (15, 36), (15, 41), (16, 21), (16, 23), (16, 33), (16, 36), (16, 37), (17, 22), (17, 24), (17, 34), (17, 37), (17, 38), (18, 23), (18, 25), (18, 35), (18, 38), (18, 39), (19, 24), (19, 26), (19, 36), (19, 39), (19, 40), (20, 25), (20, 27), (20, 37), (20, 40), (20, 41)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true))) := by
  let E : List (ℕ × ℕ) := (List.range 21).flatMap fun p =>
      ((List.range 21).filter fun w =>
        decide ((w + 21 - p) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ))).map fun w => (p, 21 + w)
  have hE : E = ([(0, 21), (0, 26), (0, 28), (0, 38), (0, 41), (1, 21), (1, 22), (1, 27), (1, 29), (1, 39), (2, 22), (2, 23), (2, 28), (2, 30), (2, 40), (3, 23), (3, 24), (3, 29), (3, 31), (3, 41), (4, 21), (4, 24), (4, 25), (4, 30), (4, 32), (5, 22), (5, 25), (5, 26), (5, 31), (5, 33), (6, 23), (6, 26), (6, 27), (6, 32), (6, 34), (7, 24), (7, 27), (7, 28), (7, 33), (7, 35), (8, 25), (8, 28), (8, 29), (8, 34), (8, 36), (9, 26), (9, 29), (9, 30), (9, 35), (9, 37), (10, 27), (10, 30), (10, 31), (10, 36), (10, 38), (11, 28), (11, 31), (11, 32), (11, 37), (11, 39), (12, 29), (12, 32), (12, 33), (12, 38), (12, 40), (13, 30), (13, 33), (13, 34), (13, 39), (13, 41), (14, 21), (14, 31), (14, 34), (14, 35), (14, 40), (15, 22), (15, 32), (15, 35), (15, 36), (15, 41), (16, 21), (16, 23), (16, 33), (16, 36), (16, 37), (17, 22), (17, 24), (17, 34), (17, 37), (17, 38), (18, 23), (18, 25), (18, 35), (18, 38), (18, 39), (19, 24), (19, 26), (19, 36), (19, 39), (19, 40), (20, 25), (20, 27), (20, 37), (20, 40), (20, 41)] : List (ℕ × ℕ)) := by decide

  let wireMap (f : Fin 42 → Fin 42) (i : ℕ) : ℕ :=
    if h : i < 42 then (f ⟨i, h⟩).val else i
  let relGate (f : Fin 42 → Fin 42) (g : Gate) : Gate :=
    ⟨g.op, g.inputs.map (wireMap f)⟩
  let relabel (f : Fin 42 → Fin 42) (C : Circuit) : Circuit :=
    ⟨C.gates.map (relGate f), wireMap f C.output⟩
  let relStep (w : List Bool) (g : Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  let relWires (f : Fin 42 → Fin 42) (u v : List Bool) : Prop :=
    42 ≤ u.length ∧ v.length = u.length ∧
      ∀ i : ℕ, v.getD (wireMap f i) false = u.getD i false
  have relStep_ok (f : Fin 42 → Fin 42) (u v : List Bool) (g : Gate)
      (h : relWires f u v) : relWires f (relStep u g) (relStep v (relGate f g)) := by
    obtain ⟨hU, hUV, hWire⟩ := h
    have hGate : (relGate f g).op.eval ((relGate f g).inputs.map fun i => v.getD i false) =
        g.op.eval (g.inputs.map fun i => u.getD i false) := by
      simp only [relGate, List.map_map]
      congr 1
      exact List.map_congr_left (fun a _ => hWire a)
    refine ⟨by simp [relStep]; omega, by simp [relStep, hUV], ?_⟩
    intro i
    simp only [relStep, hGate]
    rcases Nat.lt_trichotomy i u.length with hi | hi | hi
    · have hi' : wireMap f i < v.length := by
        unfold wireMap
        split
        · exact (f ⟨i, by assumption⟩).isLt.trans_le (hUV ▸ hU)
        · omega
      rw [List.getD_append _ _ _ _ hi', List.getD_append _ _ _ _ hi]
      exact hWire i
    · have he : wireMap f i = v.length := by
        unfold wireMap
        split <;> omega
      rw [he, hi]
      simp
    · have hmap : wireMap f i = i := by
        unfold wireMap
        split <;> omega
      rw [hmap]
      rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
  have relFold_ok (f : Fin 42 → Fin 42) (gs : List Gate) :
      ∀ (u v : List Bool), relWires f u v →
        relWires f (gs.foldl relStep u) ((gs.map (relGate f)).foldl relStep v) := by
    induction gs with
    | nil => intro u v h; exact h
    | cons g gs ih =>
      intro u v h
      exact ih _ _ (relStep_ok f u v g h)
  have relInit_ok (f : Fin 42 → Fin 42) (x : Fin 42 → Bool) :
      relWires f (List.ofFn (x ∘ f)) (List.ofFn x) := by
    refine ⟨by simp, by simp, ?_⟩
    intro i
    unfold wireMap
    split
    · rename_i hi
      rw [List.getD_eq_getElem _ _ (by simp), List.getD_eq_getElem _ _ (by simpa using hi)]
      simp only [List.getElem_ofFn, Function.comp_apply]
    · rename_i hi
      rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt hi),
        List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt hi)]
  have relabel_eval (f : Fin 42 → Fin 42) (C : Circuit) (x : Fin 42 → Bool) :
      (relabel f C).eval (List.ofFn x) = C.eval (List.ofFn (x ∘ f)) := by
    exact (relFold_ok f C.gates _ _ (relInit_ok f x)).2.2 C.output
  have relabel_mono (f : Fin 42 → Fin 42) (C : Circuit) (hC : Monotone2 C) :
      Monotone2 (relabel f C) := by
    intro g hg
    obtain ⟨g₀, hg₀, rfl⟩ := List.mem_map.mp hg
    simpa [relGate] using hC g₀ hg₀
  have relabel_size (f : Fin 42 → Fin 42) (C : Circuit) : (relabel f C).size = C.size := by
    change (C.gates.map (relGate f)).length = C.gates.length
    rw [List.length_map]
  have relabel_first (f : Fin 42 → Fin 42) (C : Circuit) (op : GateOp) (i j : Fin 42)
      (h : C.gates.head? = some (⟨op, [i.val, j.val]⟩ : Gate)) :
      (relabel f C).gates.head? = some (⟨op, [(f i).val, (f j).val]⟩ : Gate) := by
    simp [relabel, List.head?_map, h, relGate, wireMap, i.isLt, j.isLt]
  have relabel_spec (E : Fin 42 → Fin 42 → Prop) (f : Fin 42 → Fin 42) (C : Circuit)
      (hSurj : Function.Surjective f) (hEdge : ∀ i j, E (f i) (f j) ↔ E i j)
      (hC : ∀ x : Fin 42 → Bool, C.eval (List.ofFn x) = true ↔
        ∃ i j, E i j ∧ x i = true ∧ x j = true) :
      ∀ x : Fin 42 → Bool, (relabel f C).eval (List.ofFn x) = true ↔
        ∃ i j, E i j ∧ x i = true ∧ x j = true := by
    intro x
    rw [relabel_eval, hC]
    constructor
    · rintro ⟨i, j, he, hi, hj⟩
      exact ⟨f i, f j, (hEdge i j).mpr he, hi, hj⟩
    · rintro ⟨u, v, he, hu, hv⟩
      obtain ⟨i, rfl⟩ := hSurj u
      obtain ⟨j, rfl⟩ := hSurj v
      exact ⟨i, j, (hEdge i j).mp he, hu, hv⟩

  let Vertex := Fin 42

  let D : List ℕ := [0, 5, 7, 17, 20]

  let Dir (a b : Vertex) : Prop :=
    a.val < 21 ∧ 21 ≤ b.val ∧ (b.val - a.val) % 21 ∈ D

  let Adj (a b : Vertex) : Prop := Dir a b ∨ Dir b a

  letI : ∀ a b : Vertex, Decidable (Dir a b) := fun a b => by dsimp [Dir]; infer_instance

  letI : ∀ a b : Vertex, Decidable (Adj a b) := fun a b => by dsimp [Adj]; infer_instance

  let rep (a b : Vertex) : Vertex :=
    if decide (a.val < 21) = decide (b.val < 21) then 1 else if Adj a b then 21 else 22

  let wrap (i : ℕ) : Vertex := ⟨i % 42, by omega⟩

  let rot (k : Fin 21) (a : Vertex) : Vertex :=
    wrap (((a.val + k.val) % 21) + if a.val < 21 then 0 else 21)

  let dual (a : Vertex) : Vertex :=
    wrap (((42 - a.val) % 21) + if a.val < 21 then 21 else 0)

  let sq (a : Vertex) : Vertex :=
    wrap (if a.val < 21 then (2 * a.val) % 21 else 21 + (2 * a.val + 7) % 21)

  let extra (a : Vertex) : Vertex :=
    wrap (#[0, 1, 15, 12, 16, 2, 11, 13, 3, 8, 19, 20, 9, 10,
      14, 17, 4, 5, 6, 7, 18, 21, 22, 32, 33, 23, 28, 39,
      41, 29, 36, 40, 37, 30, 31, 34, 24, 25, 26, 27, 35, 38][a.val]!)

  let word (a : Vertex) : List Bool :=
    #[[], [], [false], [false, false, false, true], [false, false],
      [false, true, true, true], [false, false, false, true, false], [false, false, true, false, true, false, true], [false, false, false], [false, true, false],
      [false, true, true, false, true], [false, false, true, false], [false, false, false, true, true], [false, true, true, false], [false, false, true, false, true, false, true, false],
      [false, true], [false, false, true], [false, true, true], [false, true, false, false], [false, false, true, false, true, false],
      [false, false, true, false, true], [], [], [false, false, true], [false, true, true],
      [false, false], [false, true, false], [false, true, false, false, true], [false], [false, false, true, false, false],
      [false], [false, true, true, false, true], [false, false, true, false], [false, true, true, true], [false, true, true, false],
      [false, true, false, false, true, false, true], [false, true], [false, true, false], [false, true, true], [false, true, false, false],
      [false, true, false, false, true, false], [false, true]][a.val]!

  let wordMap (a v : Vertex) : Vertex :=
    (word a).foldl (fun w step => if step then extra w else sq w) v

  let Auto (f : Vertex → Vertex) : Prop :=
    (∀ a b, f a = f b → a = b) ∧ ∀ a b, Adj (f a) (f b) ↔ Adj a b

  letI : ∀ f : Vertex → Vertex, Decidable (Auto f) := fun f => by dsimp [Auto]; infer_instance

  have auto_comp {f g : Vertex → Vertex} (hf : Auto f) (hg : Auto g) : Auto (f ∘ g) :=
    ⟨fun a b h => hg.1 a b (hf.1 (g a) (g b) h),
      fun a b => (hf.2 (g a) (g b)).trans (hg.2 a b)⟩

  have rot_auto : ∀ k : Fin 21, Auto (rot k) := by decide

  have fixed_autos : Auto dual ∧ Auto sq ∧ Auto extra := by decide

  have word_auto (a : Vertex) : Auto (wordMap a) := by
    have hfold (xs : List Bool) (f : Vertex → Vertex) (hf : Auto f) :
        Auto (fun x => xs.foldl (fun w step => if step then extra w else sq w) (f x)) := by
      induction xs generalizing f with
      | nil => exact hf
      | cons b xs ih =>
        cases b
        · exact ih (sq ∘ f) (auto_comp fixed_autos.2.1 hf)
        · exact ih (extra ∘ f) (auto_comp fixed_autos.2.2 hf)
    exact hfold (word a) id ⟨fun _ _ h => h, fun _ _ => Iff.rfl⟩

  have word_endpoints : ∀ a : Vertex, wordMap a 0 = 0 ∧ (a ≠ 0 → wordMap a (rep 0 a) = a) := by
    decide +kernel

  let forward (a : Vertex) : Fin 21 := ⟨a.val % 21, by omega⟩

  let backward (a : Vertex) : Fin 21 := ⟨(21 - a.val) % 21, by omega⟩

  have center_facts : ∀ a b : Vertex, a.val < 21 → a ≠ b →
      let u := rot (backward a) b
      rot (forward a) 0 = a ∧ u ≠ 0 ∧ rep 0 u = rep a b ∧ rot (forward a) u = b := by
    decide +kernel

  have dual_facts : ∀ a b : Vertex, ¬ a.val < 21 →
      (dual a).val < 21 ∧ dual (dual a) = a ∧ dual (dual b) = b ∧ rep (dual a) (dual b) = rep a b := by
    decide +kernel

  have orbit_point (a b : Vertex) (ha : a.val < 21) (hne : a ≠ b) :
      ∃ f : Vertex → Vertex, Auto f ∧ f 0 = a ∧ f (rep a b) = b := by
    let u := rot (backward a) b
    obtain ⟨ha', hu, hre, hb'⟩ := center_facts a b ha hne
    refine ⟨rot (forward a) ∘ wordMap u, auto_comp (rot_auto _) (word_auto _), ?_, ?_⟩
    · change rot (forward a) (wordMap u 0) = a
      rw [(word_endpoints u).1, ha']
    · change rot (forward a) (wordMap u (rep a b)) = b
      change u ≠ 0 at hu
      change rep 0 u = rep a b at hre
      change rot (forward a) u = b at hb'
      rw [← hre, (word_endpoints u).2 hu, hb']

  have orbit (a b : Vertex) (hne : a ≠ b) : ∃ f : Vertex ≃ Vertex,
      (∀ u v, Adj (f u) (f v) ↔ Adj u v) ∧ f 0 = a ∧ f (rep a b) = b := by
    have pack (g : Vertex → Vertex) (hg : Auto g) (ha : g 0 = a) (hb : g (rep a b) = b) :
        ∃ f : Vertex ≃ Vertex, (∀ u v, Adj (f u) (f v) ↔ Adj u v) ∧ f 0 = a ∧ f (rep a b) = b := by
      have hi : Function.Injective g := fun _ _ h => hg.1 _ _ h
      let f := Equiv.ofBijective g ⟨hi, Finite.surjective_of_injective hi⟩
      exact ⟨f, hg.2, ha, hb⟩
    by_cases ha : a.val < 21
    · obtain ⟨f, hf, ha, hb⟩ := orbit_point a b ha hne
      exact pack f hf ha hb
    · obtain ⟨hpoint, hda, hdb, hrep⟩ := dual_facts a b ha
      have hdn : dual a ≠ dual b := fun h => hne (fixed_autos.1.1 _ _ h)
      obtain ⟨f, hf, ha', hb'⟩ := orbit_point (dual a) (dual b) hpoint hdn
      refine pack (dual ∘ f) (auto_comp fixed_autos.1 hf) ?_ ?_
      · exact congrArg dual ha' |>.trans hda
      · change dual (f (rep a b)) = b
        rw [← hrep, hb', hdb]

  have compactDir (a b : Fin 42) : (a.val, b.val) ∈ E ↔ Dir a b := by
    simp only [E, Dir, List.mem_flatMap, List.mem_map, List.mem_filter,
      decide_eq_true_eq, List.mem_range, Prod.mk.injEq]
    constructor
    · rintro ⟨p, hp, w, ⟨hw, hD⟩, ⟨hpa, hv⟩⟩
      refine ⟨by omega, by omega, ?_⟩
      have he : (b.val - a.val) % 21 = (w + 21 - p) % 21 := by omega
      rw [he]
      exact hD
    · rintro ⟨hp, hv, hD⟩
      let w := b.val - 21
      have hwb : 21 + w = b.val := by dsimp [w]; omega
      refine ⟨a.val, hp, w, ⟨by have := b.isLt; dsimp [w]; omega, ?_⟩, rfl, hwb⟩
      have he : (w + 21 - a.val) % 21 = (b.val - a.val) % 21 := by omega
      rw [he]
      exact hD
  have compactAdj (u v : Fin 42) : Adj u v ↔ (u.val, v.val) ∈ E ∨ (v.val, u.val) ∈ E := by
    change (Dir u v ∨ Dir v u) ↔ _
    rw [compactDir u v, compactDir v u]
  have pred (x : Fin 42 → Bool) :
      (∃ u v : Fin 42, (u.val, v.val) ∈ E ∧ x u = true ∧ x v = true) ↔
      (∃ u v : Fin 42, Adj u v ∧ x u = true ∧ x v = true) := by
    constructor
    · rintro ⟨u, v, he, hu, hv⟩
      exact ⟨u, v, (compactAdj u v).mpr (.inl he), hu, hv⟩
    · rintro ⟨u, v, he, hu, hv⟩
      rcases (compactAdj u v).mp he with he | he
      · exact ⟨u, v, he, hu, hv⟩
      · exact ⟨v, u, he, hv, hu⟩
  have repInc (u v : Fin 42) (he : Adj u v) : rep u v = 21 := by
    have hSides : decide (u.val < 21) ≠ decide (v.val < 21) := by
      change Dir u v ∨ Dir v u at he
      rcases he with h | h
      · simp [h.1, Nat.not_lt.mpr h.2.1]
      · simp [h.1, Nat.not_lt.mpr h.2.1]
    unfold rep
    rw [if_neg hSides, if_pos he]
  have reps (u v : Fin 42) : rep u v = 1 ∨ rep u v = 21 ∨ rep u v = 22 := by
    unfold rep
    split_ifs <;> simp

  have normalizeFor (C : Circuit) (hC : Monotone2 C)
      (hFun : ∀ x : Fin 42 → Bool, C.eval (List.ofFn x) = true ↔
        ∃ u v : Fin 42, (u.val, v.val) ∈ E ∧ x u = true ∧ x v = true) :
      ∃ (F : Circuit) (u v : Fin 42) (op : GateOp),
        Monotone2 F ∧ F.size ≤ C.size ∧
        (∀ x : Fin 42 → Bool, F.eval (List.ofFn x) = true ↔
          ∃ u v : Fin 42, (u.val, v.val) ∈ E ∧ x u = true ∧ x v = true) ∧
        u ≠ v ∧ F.gates.head? = some ⟨op, [u.val, v.val]⟩ ∧
        (op = .or ∨ op = .and ∧ Adj u v) := by
    obtain ⟨F, u, v, op, hF, hs, he, hn, hh, ho⟩ := normalize C hC hFun
    refine ⟨F, u, v, op, hF, hs, he, hn, hh, ho.imp id ?_⟩
    rintro ⟨h, ha⟩
    exact ⟨h, (compactAdj u v).mpr ha⟩

  classical
  rintro ⟨C₀, hC₀, hsize₀, hfun₀⟩
  let computes (C : Circuit) : Prop := ∀ x : Fin 42 → Bool, C.eval (List.ofFn x) = true ↔
    ∃ u v : Fin 42, (u.val, v.val) ∈ E ∧ x u = true ∧ x v = true
  have hfun₀' : computes C₀ := by
    dsimp [computes]
    simpa only [hE] using hfun₀
  let sizeAvailable (k : ℕ) : Prop := ∃ C : Circuit, Monotone2 C ∧ C.size = k ∧ computes C
  have hEx : ∃ k, sizeAvailable k := ⟨C₀.size, C₀, hC₀, rfl, hfun₀'⟩
  obtain ⟨C, hC, hSizeC, hFuncC⟩ := Nat.find_spec hEx
  have hleast (Q : Circuit) (hQ : Monotone2 Q) (he : computes Q) : C.size ≤ Q.size := by
    rw [hSizeC]
    exact Nat.find_min' hEx ⟨Q, hQ, rfl, he⟩
  obtain ⟨F, u, v, op, hF, hFSize, hFunF, hne, hHead, hOp⟩ := normalizeFor C hC hFuncC
  obtain ⟨σ, hσ, hσ0, hσrep⟩ := orbit u v hne
  let G := relabel σ.symm F
  have hG : Monotone2 G := relabel_mono _ _ hF
  have hGSize : G.size ≤ C.size := (relabel_size _ _).le.trans hFSize
  have hGSize' : G.size ≤ 124 := hGSize.trans ((hleast C₀ hC₀ hfun₀').trans hsize₀)
  have hInv (i j : Fin 42) : Adj (σ.symm i) (σ.symm j) ↔ Adj i j := by
    simpa only [Equiv.apply_symm_apply] using (hσ (σ.symm i) (σ.symm j)).symm
  have hFunG : computes G := by
    intro x
    exact (relabel_spec Adj σ.symm F σ.symm.surjective hInv
      (fun y => (hFunF y).trans (pred y)) x).trans (pred x).symm
  have hLeastG (Q : Circuit) (hQ : Monotone2 Q) (he : computes Q) : G.size ≤ Q.size :=
    hGSize.trans (hleast Q hQ he)
  have hu : σ.symm u = 0 := by rw [← hσ0, Equiv.symm_apply_apply]
  have hv : σ.symm v = rep u v :=
    (congrArg σ.symm hσrep.symm).trans (σ.symm_apply_apply (rep u v))
  have hFirst : G.gates.head? = some ⟨op, [0, (rep u v).val]⟩ := by
    simpa only [hu, hv, Fin.val_zero] using relabel_first σ.symm F op u v hHead
  rcases hOp with ho | ⟨ha, he⟩
  · rcases reps u v with hr | hr | hr
    · exact noSame ⟨G, hG, hGSize', hFunG, (by simpa [ho, hr] using hFirst), hLeastG⟩
    · exact noCross ⟨G, hG, hGSize', hFunG, Or.inl (by simpa [ho, hr] using hFirst), hLeastG⟩
    · exact noCross ⟨G, hG, hGSize', hFunG, Or.inr (by simpa [ho, hr] using hFirst), hLeastG⟩
  · have hr := repInc u v he
    exact noAnd ⟨G, hG, hGSize', hFunG, (by simpa [ha, hr] using hFirst), hLeastG⟩
