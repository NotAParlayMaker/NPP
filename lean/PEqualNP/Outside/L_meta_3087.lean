import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3087_aux

open PEqualNP.CircuitLowerBounds

def ev (g : Gate) (v : List Bool) : Bool := g.op.eval (g.inputs.map fun i => v.getD i false)

def stepF (w : List Bool) (g : Gate) : List Bool := w ++ [ev g w]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl stepF x := rfl

theorem fold_len (gs : List Gate) (w : List Bool) :
    (gs.foldl stepF w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => simp [List.foldl, ih, stepF]; omega

theorem fold_agree (B : ℕ → Prop) : ∀ (gs gs' : List Gate) (w w' : List Bool),
    gs.length = gs'.length → w.length = w'.length →
    (∀ p, ¬ B p → w.getD p false = w'.getD p false) →
    (∀ j (hj : j < gs.length) (hj' : j < gs'.length) (v v' : List Bool),
      v.length = w.length + j → v'.length = w.length + j →
      (∀ p, ¬ B p → v.getD p false = v'.getD p false) → ¬ B (w.length + j) →
      ev gs[j] v = ev gs'[j] v') →
    ∀ p, ¬ B p → (gs.foldl stepF w).getD p false = (gs'.foldl stepF w').getD p false := by
  intro gs
  induction gs with
  | nil =>
    intro gs' w w' hl hw hagree _
    cases gs' with
    | nil => simpa using hagree
    | cons _ _ => simp at hl
  | cons g gs ih =>
    intro gs' w w' hl hw hagree hg
    cases gs' with
    | nil => simp at hl
    | cons g' gs' =>
      simp only [List.foldl]
      apply ih gs' (stepF w g) (stepF w' g') (by simpa using hl) (by simp [stepF, hw])
      · intro p hp
        simp only [stepF]
        rcases lt_trichotomy p w.length with h | h | h
        · rw [List.getD_append _ _ _ _ h, List.getD_append _ _ _ _ (hw ▸ h)]; exact hagree p hp
        · subst h
          rw [List.getD_append_right _ _ _ _ le_rfl, List.getD_append_right _ _ _ _ (le_of_eq hw.symm)]
          rw [hw, Nat.sub_self]
          exact hg 0 (by simp) (by simp) w w' rfl hw.symm hagree (by simpa using hp)
        · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
      · intro j hj hj' v v' hv hv' hvv hb
        have := hg (j+1) (by simp; omega) (by simp; omega) v v' (by simp [stepF] at hv; omega)
          (by simp [stepF] at hv'; omega) hvv (by simp [stepF] at hb; rwa [Nat.add_assoc, Nat.add_comm 1] at hb)
        simpa using this

theorem ev_congr' (g : Gate) (v v' : List Bool)
    (h : ∀ i ∈ g.inputs, v.getD i false = v'.getD i false) : ev g v = ev g v' := by
  unfold ev
  rw [List.map_congr_left h]

def clampG (N : ℕ) : Gate → Gate
  | ⟨GateOp.not, l⟩ => ⟨GateOp.not, (l.take 1).map (min · N)⟩
  | ⟨op, l⟩ => ⟨op, l.map (min · N)⟩

theorem getD_min (v : List Bool) (N i : ℕ) (h : v.length ≤ N) :
    v.getD (min i N) false = v.getD i false := by
  rcases le_total i N with h1 | h1
  · rw [min_eq_left h1]
  · rw [min_eq_right h1, List.getD_eq_default _ _ h, List.getD_eq_default _ _ (h.trans h1)]

theorem ev_clamp (N : ℕ) (g : Gate) (v : List Bool) (h : v.length ≤ N) :
    ev (clampG N g) v = ev g v := by
  have hm : ∀ l : List ℕ, (l.map (min · N)).map (fun i => v.getD i false)
      = l.map (fun i => v.getD i false) := by
    intro l
    rw [List.map_map]
    apply List.map_congr_left
    intro a _
    exact getD_min v N a h
  rcases g with ⟨op, l⟩
  cases op <;> simp only [clampG, ev, hm]
  rcases l with _ | ⟨a, l⟩ <;> simp [GateOp.eval]

def Inv (C : Circuit) : Prop :=
  (∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
    g.inputs.length ≤ 2 ∧ (g.op = GateOp.not → g.inputs.length ≤ 1) ∧
    ∀ i ∈ g.inputs, i ≤ 10 + C.gates.length) ∧ C.output ≤ 10 + C.gates.length

def M (C : Circuit) : ℕ :=
  ((Finset.range C.gates.length).filter
    (fun j => (C.gates[j]?).map Gate.inputs ≠ some [10 + j])).card

theorem step_sem (C : Circuit) (j : ℕ) (hj : j < C.gates.length)
    (hn : 10 + j ∉ C.output :: C.gates.flatMap Gate.inputs) (x : List Bool) (hx : x.length = 10) :
    (Circuit.mk (C.gates.set j ⟨GateOp.or, [10 + j]⟩) C.output).eval x = C.eval x := by
  simp only [Circuit.eval, wires_eq]
  refine fold_agree (· = 10 + j) (C.gates.set j ⟨GateOp.or, [10 + j]⟩) C.gates x x (by simp) rfl
    (fun _ _ => rfl) ?_ C.output ?_
  · intro j' hj1 hj2 v v' hv hv' hvv hb
    have hne : j ≠ j' := by
      rintro rfl
      exact hb (by rw [hx])
    rw [List.getElem_set_ne hne]
    apply ev_congr'
    intro i hi
    apply hvv
    rintro rfl
    exact hn (List.mem_cons_of_mem _ (List.mem_flatMap.2 ⟨_, List.getElem_mem hj2, hi⟩))
  · intro h
    apply hn
    rw [← h]
    exact List.mem_cons_self ..

theorem step_M (C : Circuit) (j : ℕ) (hj : j < C.gates.length)
    (hn : 10 + j ∉ C.output :: C.gates.flatMap Gate.inputs) :
    M (Circuit.mk (C.gates.set j ⟨GateOp.or, [10 + j]⟩) C.output) < M C := by
  unfold M
  simp only [List.length_set]
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨j, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_range]
      refine ⟨hj, ?_⟩
      rw [List.getElem?_eq_getElem hj]
      intro h
      simp only [Option.map_some, Option.some.injEq] at h
      apply hn
      refine List.mem_cons_of_mem _ (List.mem_flatMap.2 ⟨_, List.getElem_mem hj, ?_⟩)
      rw [h]
      exact List.mem_singleton_self _
    · simp [List.getElem?_set, hj]
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_range] at hk ⊢
    refine ⟨hk.1, ?_⟩
    have := hk.2
    rw [List.getElem?_set] at this
    split_ifs at this with h1
    · subst h1
      simp at this
    · exact this

theorem step_inv (C : Circuit) (j : ℕ) (hj : j < C.gates.length) (hC : Inv C) :
    Inv (Circuit.mk (C.gates.set j ⟨GateOp.or, [10 + j]⟩) C.output) := by
  refine ⟨?_, ?_⟩
  · intro g hg
    simp only [List.length_set] at hg ⊢
    rcases List.mem_or_eq_of_mem_set hg with h | h
    · exact hC.1 g h
    · subst h
      simp
      omega
  · simpa using hC.2

theorem loop : ∀ m (C : Circuit), M C ≤ m → Inv C → ∃ D : Circuit, Inv D ∧
    D.gates.length = C.gates.length ∧ (∀ x : List Bool, x.length = 10 → D.eval x = C.eval x) ∧
    ∀ j < D.gates.length, 10 + j ∈ D.output :: D.gates.flatMap Gate.inputs := by
  intro m
  induction m with
  | zero =>
    intro C hM hC
    refine ⟨C, hC, rfl, fun _ _ => rfl, ?_⟩
    intro j hj
    by_contra hn
    have := step_M C j hj hn
    omega
  | succ m ih =>
    intro C hM hC
    by_cases hall : ∀ j < C.gates.length, 10 + j ∈ C.output :: C.gates.flatMap Gate.inputs
    · exact ⟨C, hC, rfl, fun _ _ => rfl, hall⟩
    · push_neg at hall
      obtain ⟨j, hj, hn⟩ := hall
      have := step_M C j hj hn
      obtain ⟨D, h1, h2, h3, h4⟩ := ih _ (by omega) (step_inv C j hj hC)
      refine ⟨D, h1, by simpa using h2, fun x hx => ?_, h4⟩
      rw [h3 x hx, step_sem C j hj hn x hx]

theorem clamp_sem (C : Circuit) (x : List Bool) (hx : x.length = 10) :
    (Circuit.mk (C.gates.map (clampG (10 + C.gates.length)))
      (min C.output (10 + C.gates.length))).eval x = C.eval x := by
  simp only [Circuit.eval, wires_eq]
  have hlen : (C.gates.foldl stepF x).length = 10 + C.gates.length := by rw [fold_len, hx]
  have := fold_agree (fun _ => False) (C.gates.map (clampG (10 + C.gates.length))) C.gates x x
    (by simp) rfl (fun _ _ => rfl) ?_
  · rw [this _ (fun h => h), ← hlen, getD_min _ _ _ le_rfl]
  · intro j hj1 hj2 v v' hv hv' hvv _
    rw [List.getElem_map, ev_clamp _ _ _ (by rw [hv, hx]; omega)]
    exact ev_congr' _ _ _ (fun i _ => hvv i (fun h => h))

theorem clamp_inv (C : Circuit) (hC : PEqualNP.MetaComplexity.FanInTwo C) :
    Inv (Circuit.mk (C.gates.map (clampG (10 + C.gates.length)))
      (min C.output (10 + C.gates.length))) := by
  refine ⟨?_, ?_⟩
  · intro g' hg'
    simp only [List.length_map] at hg' ⊢
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hg'
    obtain ⟨hop, hl⟩ := hC g hg
    rcases g with ⟨op, l⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    simp only at hl
    rcases hop with rfl | rfl | rfl <;>
      refine ⟨by simp [clampG], by simp [clampG] <;> omega, by simp [clampG], ?_⟩ <;>
      intro i hi <;> simp only [clampG, List.mem_map] at hi <;> obtain ⟨a, _, rfl⟩ := hi <;>
      exact min_le_right _ _
  · simp

theorem budget (gs : List Gate) (h : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨
    g.op = GateOp.not) ∧ g.inputs.length ≤ 2 ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)) :
    (gs.filter (fun g => g.op.eval [false] && !g.op.eval [true])).length
      + (gs.flatMap Gate.inputs).length ≤ 2 * gs.length := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    have ih' := ih (fun g' hg' => h g' (List.mem_cons_of_mem _ hg'))
    obtain ⟨hop, hl, hn⟩ := h g (List.mem_cons_self ..)
    rcases g with ⟨op, l⟩
    simp only at hop hl hn
    rw [List.filter_cons, List.flatMap_cons, List.length_append, List.length_cons]
    rcases hop with rfl | rfl | rfl
    · rw [if_neg (by simp [GateOp.eval])]
      dsimp only
      omega
    · rw [if_neg (by simp [GateOp.eval])]
      dsimp only
      omega
    · rw [if_pos (by simp [GateOp.eval]), List.length_cons]
      have := hn rfl
      dsimp only
      omega

theorem sum_count_le (L : List ℕ) (S : Finset ℕ) : ∑ v ∈ S, L.count v ≤ L.length := by
  induction L with
  | nil => simp
  | cons a L ih =>
    calc ∑ v ∈ S, (a :: L).count v ≤ ∑ v ∈ S, (L.count v + if v = a then 1 else 0) := by
          apply Finset.sum_le_sum
          intro v _
          rcases eq_or_ne v a with rfl | h
          · simp [List.count_cons]
          · simp [List.count_cons, h, h.symm]
      _ = ∑ v ∈ S, L.count v + ∑ v ∈ S, (if v = a then 1 else 0) := Finset.sum_add_distrib
      _ ≤ L.length + 1 := by
          apply add_le_add ih
          rw [Finset.sum_ite_eq']
          split_ifs <;> simp
      _ = (a :: L).length := rfl

theorem getD_ofFn (x : Fin 10 → Bool) (p : ℕ) :
    (List.ofFn x).getD p false = if h : p < 10 then x ⟨p, h⟩ else false := by
  split_ifs with h
  · rw [List.getD_eq_getElem _ _ (by simpa using h), List.getElem_ofFn]
  · exact List.getD_eq_default _ _ (by simp; omega)

theorem input_used (D : Circuit) (i : ℕ) (hi : i < 10) (x y : Fin 10 → Bool)
    (hxy : ∀ k : Fin 10, k ≠ ⟨i, hi⟩ → x k = y k)
    (hne : D.eval (List.ofFn x) ≠ D.eval (List.ofFn y)) :
    i ∈ D.output :: D.gates.flatMap Gate.inputs := by
  by_contra hn
  apply hne
  simp only [Circuit.eval, wires_eq]
  refine fold_agree (· = i) D.gates D.gates _ _ rfl (by simp) ?_ ?_ D.output ?_
  · intro p hp
    rw [getD_ofFn, getD_ofFn]
    split_ifs with h
    · exact hxy _ (fun e => hp (by simpa using congrArg Fin.val e))
    · rfl
  · intro j hj _ v v' hv hv' hvv _
    apply ev_congr'
    intro k hk
    apply hvv
    rintro rfl
    exact hn (List.mem_cons_of_mem _ (List.mem_flatMap.2 ⟨_, List.getElem_mem hj, hk⟩))
  · intro h
    apply hn
    rw [← h]
    exact List.mem_cons_self ..

end PEqualNP.Outside.L_meta_3087_aux

theorem PEqualNP.Outside.L_meta_3087 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x3 : Fin (10 : ℕ)), ∃ (x4 : Fin (10 : ℕ) → Bool) (x5 : Fin (10 : ℕ) → Bool), (∀ (x6 : Fin (10 : ℕ)), x6 ≠ x3 → x4 x6 = x5 x6) ∧ PEqualNP.MetaComplexity.circuitFun (10 : ℕ) x1 x4 ≠ PEqualNP.MetaComplexity.circuitFun (10 : ℕ) x1 x5) → ∃ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x4 ∧ PEqualNP.MetaComplexity.circuitFun (10 : ℕ) x4 = PEqualNP.MetaComplexity.circuitFun (10 : ℕ) x1 ∧ x4.size ≤ x1.size ∧ (x4.output ≤ (10 : ℕ) + x4.size ∧ ∀ x5 ∈ x4.gates, ∀ x7 ∈ x5.inputs, x7 ≤ (10 : ℕ) + x4.size) ∧ (∀ x5 < (10 : ℕ) + x4.size, x5 ∈ x4.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x4.gates) ∧ (9 : ℕ) + (List.filter (fun (x5 : PEqualNP.CircuitLowerBounds.Gate) => x5.op.eval [Bool.false] && !x5.op.eval [Bool.true]) x4.gates).length + ∑ x5 ∈ Finset.range ((10 : ℕ) + x4.size), (List.count x5 (x4.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x4.gates) - (1 : ℕ)) ≤ x4.size := by
  intro C hC hdep
  have hinv := PEqualNP.Outside.L_meta_3087_aux.clamp_inv C hC
  obtain ⟨D, hD, hlen, hev, href⟩ := PEqualNP.Outside.L_meta_3087_aux.loop _ _ le_rfl hinv
  have hfun : PEqualNP.MetaComplexity.circuitFun 10 D = PEqualNP.MetaComplexity.circuitFun 10 C := by
    funext x
    simp only [PEqualNP.MetaComplexity.circuitFun]
    rw [hev _ (by simp), PEqualNP.Outside.L_meta_3087_aux.clamp_sem C _ (by simp)]
  have hsz : D.gates.length = C.gates.length := by simpa using hlen
  have hused : ∀ v < 10 + D.gates.length,
      v ∈ D.output :: D.gates.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs := by
    intro v hv
    by_cases h10 : v < 10
    · obtain ⟨x, y, hxy, hne⟩ := hdep ⟨v, h10⟩
      rw [← hfun] at hne
      exact PEqualNP.Outside.L_meta_3087_aux.input_used D v h10 x y hxy hne
    · obtain ⟨j, rfl⟩ : ∃ j, v = 10 + j := ⟨v - 10, by omega⟩
      exact href j (by omega)
  refine ⟨D, ?_, hfun, ?_, ⟨hD.2, ?_⟩, hused, ?_⟩
  · intro g hg
    obtain ⟨hop, hl, _⟩ := hD.1 g hg
    refine ⟨?_, hl⟩
    rcases hop with h | h | h <;> simp [h]
  · show D.gates.length ≤ C.gates.length
    omega
  · intro g hg i hi
    exact (hD.1 g hg).2.2.2 i hi
  · have hb := PEqualNP.Outside.L_meta_3087_aux.budget D.gates
      (fun g hg => ⟨(hD.1 g hg).1, (hD.1 g hg).2.1, (hD.1 g hg).2.2.1⟩)
    have hs := PEqualNP.Outside.L_meta_3087_aux.sum_count_le
      (D.output :: D.gates.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs)
      (Finset.range (10 + D.size))
    have hpos : ∀ v ∈ Finset.range (10 + D.size),
        1 ≤ (D.output :: D.gates.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs).count v :=
      fun v hv => List.count_pos_iff.2 (hused v (by simpa [PEqualNP.CircuitLowerBounds.Circuit.size] using hv))
    have key : ∑ v ∈ Finset.range (10 + D.size),
        ((D.output :: D.gates.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs).count v - 1)
        + ∑ v ∈ Finset.range (10 + D.size), 1
        = ∑ v ∈ Finset.range (10 + D.size),
          (D.output :: D.gates.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs).count v := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun v hv => Nat.sub_add_cancel (hpos v hv))
    rw [Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one] at key
    simp only [List.length_cons, PEqualNP.CircuitLowerBounds.Circuit.size] at hs key hb ⊢
    omega
