import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1586

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def val (gs : List Gate) (x : List Bool) (Y : ℕ) : Bool :=
  (gs.foldl step x).getD Y false

lemma eval_eq (gs : List Gate) (Y : ℕ) (x : List Bool) :
    Circuit.eval ⟨gs, Y⟩ x = val gs x Y := rfl

lemma foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, step, List.length_append, List.length_cons, List.length_nil]
    omega

lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < w.length) :
    (gs.foldl step w).getD j false = w.getD j false := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    · simp [step, List.getD_eq_getElem?_getD, List.getElem?_append_left hj]
    · simp only [step, List.length_append, List.length_cons, List.length_nil]
      omega

lemma val_input (gs : List Gate) (x : List Bool) (Y : ℕ) (hY : Y < x.length) :
    val gs x Y = x.getD Y false :=
  foldl_getD_lt gs x Y hY

lemma val_big (gs : List Gate) (x : List Bool) (Y : ℕ) (hY : x.length + gs.length ≤ Y) :
    val gs x Y = false := by
  unfold val
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none]
  · rfl
  · rw [foldl_length]
    exact hY

lemma val_gate (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < gs.length)
    (hwf : ∀ a ∈ (gs[i]).inputs, a < x.length + i) :
    val gs x (x.length + i) = (gs[i]).op.eval ((gs[i]).inputs.map (val gs x)) := by
  have hsplit : gs = gs.take i ++ gs[i] :: gs.drop (i + 1) := by simp
  have hlen : ((gs.take i).foldl step x).length = x.length + i := by
    rw [foldl_length, List.length_take]
    omega
  have hpre : ∀ a, a < x.length + i →
      val gs x a = ((gs.take i).foldl step x).getD a false := by
    intro a ha
    unfold val
    conv_lhs => rw [← List.take_append_drop i gs, List.foldl_append]
    exact foldl_getD_lt _ _ _ (by omega)
  have hmap : (gs[i]).inputs.map (val gs x) =
      (gs[i]).inputs.map (fun a => ((gs.take i).foldl step x).getD a false) :=
    List.map_congr_left fun a ha => hpre a (hwf a ha)
  rw [hmap]
  unfold val
  conv_lhs => rw [hsplit, List.foldl_append, List.foldl_cons]
  rw [foldl_getD_lt]
  · rw [← hlen]
    simp [step, List.getD_eq_getElem?_getD]
  · simp only [step, List.length_append, List.length_cons, List.length_nil]
    omega

def Top (gates : List Gate) (N u Y : ℕ) : Prop :=
  ∀ S : Set ℕ, u ∈ S → (∀ i : Fin gates.length, N + (i : ℕ) ∈ S →
    (gates.get i).op = GateOp.or → ∀ a ∈ (gates.get i).inputs, a ∈ S) → Y ∈ S

lemma top_closed (gates : List Gate) (N u : ℕ) (i : Fin gates.length)
    (h : Top gates N u (N + (i : ℕ))) (hor : (gates.get i).op = GateOp.or)
    (a : ℕ) (ha : a ∈ (gates.get i).inputs) : Top gates N u a :=
  fun S hu hc => hc i (h S hu hc) hor a ha

lemma top_false (gates : List Gate) (N u : ℕ) (x : List Bool) (hx : x.length = N)
    (hwf : ∀ i : Fin gates.length, ∀ a ∈ (gates.get i).inputs, a < N + (i : ℕ))
    (hu : val gates x u = false) (Y : ℕ) (hY : Top gates N u Y) :
    val gates x Y = false := by
  refine hY {Z | val gates x Z = false} hu ?_
  intro i hi hor a ha
  have hg := val_gate gates x i i.2 (by
    intro b hb
    rw [hx]
    exact hwf i b hb)
  rw [hx] at hg
  have hi' : val gates x (N + (i : ℕ)) = false := hi
  rw [hg] at hi'
  have hor' : (gates[(i : ℕ)]).op = GateOp.or := hor
  rw [hor'] at hi'
  simp only [GateOp.eval, List.any_eq_false, List.mem_map, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂] at hi'
  have := hi' a ha
  simpa using this

lemma top_rim (gates : List Gate) (N u r : ℕ) (x : List Bool) (hx : x.length = N)
    (hops : ∀ g ∈ gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (hwf : ∀ i : Fin gates.length, ∀ a ∈ (gates.get i).inputs, a < N + (i : ℕ))
    (hin : ∀ Y, Y < N → Top gates N u Y → x.getD Y false = true → Y = r) :
    ∀ Y, Top gates N u Y → val gates x Y = true →
      Top gates N u r ∨ ∃ a : ℕ, Top gates N u a ∧
        (∃ i : Fin gates.length, a = N + (i : ℕ) ∧ (gates.get i).op = GateOp.and) ∧
        val gates x a = true := by
  intro Y
  induction Y using Nat.strong_induction_on with
  | _ Y ih =>
    intro hY hv
    by_cases h1 : Y < N
    · rw [val_input gates x Y (by omega)] at hv
      have := hin Y h1 hY hv
      subst this
      exact Or.inl hY
    · by_cases h2 : Y - N < gates.length
      · let i : Fin gates.length := ⟨Y - N, h2⟩
        have hYi : Y = N + (i : ℕ) := by
          change Y = N + (Y - N)
          omega
        rcases hops (gates.get i) (List.get_mem _ _) with hand | hor
        · exact Or.inr ⟨Y, hY, ⟨i, hYi, hand⟩, hv⟩
        · have hg := val_gate gates x i i.2 (by
            intro b hb
            rw [hx]
            exact hwf i b hb)
          rw [hx, ← hYi, hv] at hg
          have hor' : (gates[(i : ℕ)]).op = GateOp.or := hor
          rw [hor'] at hg
          have hg' := hg.symm
          simp only [GateOp.eval, List.any_eq_true, List.mem_map] at hg'
          obtain ⟨b, ⟨a, ha, rfl⟩, hb⟩ := hg'
          have halt : a < Y := by
            rw [hYi]
            exact hwf i a ha
          have hYtop : Top gates N u (N + (i : ℕ)) := by
            rw [← hYi]
            exact hY
          exact ih a halt (top_closed gates N u i hYtop hor a ha) (by simpa using hb)
      · rw [val_big gates x Y (by omega)] at hv
        exact absurd hv (by simp)

lemma and_input (gates : List Gate) (N : ℕ) (x : List Bool) (hx : x.length = N)
    (hwf : ∀ i : Fin gates.length, ∀ a ∈ (gates.get i).inputs, a < N + (i : ℕ))
    (i : Fin gates.length) (hand : (gates.get i).op = GateOp.and)
    (hv : val gates x (N + (i : ℕ)) = true) (c : ℕ) (hc : c ∈ (gates.get i).inputs) :
    val gates x c = true := by
  have hg := val_gate gates x i i.2 (by
    intro b hb
    rw [hx]
    exact hwf i b hb)
  rw [hx, hv] at hg
  have hand' : (gates[(i : ℕ)]).op = GateOp.and := hand
  rw [hand'] at hg
  have hg' := hg.symm
  simp only [GateOp.eval, List.all_eq_true, List.mem_map, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂] at hg'
  have := hg' c hc
  simpa using this

lemma getD_ofFn {N : ℕ} (f : Fin N → Bool) (j : ℕ) (hj : j < N) :
    (List.ofFn f).getD j false = f ⟨j, hj⟩ := by
  simp [List.getD_eq_getElem?_getD, hj]

end PEqualNP.Outside.L_meta_1586

theorem PEqualNP.Outside.L_meta_1586 : ∀ (q m N : ℕ) (L : Fin N → Finset (Fin N)) (i0 : Fin N) (T0 : Finset (Fin N)),
    3 ≤ q → 3 ≤ m → m ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    T0 ⊆ L i0 → T0.card = m →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (u : ℕ),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length ∧ ∀ a ∈ (gates.get i).inputs, a < N + (i : ℕ)) →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, u⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0))) = false →
    (∀ Y : ℕ, (∀ S : Set ℕ, u ∈ S → (∀ i : Fin gates.length, N + (i : ℕ) ∈ S → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ a ∈ (gates.get i).inputs, a ∈ S) → Y ∈ S) → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, Y⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0))) = false) ∧
    (∀ p : Fin N, (∀ S : Set ℕ, u ∈ S → (∀ i : Fin gates.length, N + (i : ℕ) ∈ S → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ a ∈ (gates.get i).inputs, a ∈ S) → (p : ℕ) ∈ S) → p ∈ L i0) ∧
    (∀ r ∈ L i0 \ T0, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, u⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0 ∨ v = r))) = true →
      (∀ S : Set ℕ, u ∈ S → (∀ i : Fin gates.length, N + (i : ℕ) ∈ S → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ a ∈ (gates.get i).inputs, a ∈ S) → (r : ℕ) ∈ S) ∨ ∃ a : ℕ, (∀ S : Set ℕ, u ∈ S → (∀ i : Fin gates.length, N + (i : ℕ) ∈ S → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ a ∈ (gates.get i).inputs, a ∈ S) → a ∈ S) ∧ (∃ i : Fin gates.length, a = N + (i : ℕ) ∧ (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and) ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, a⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0 ∨ v = r))) = true) ∧
    (∀ (a : Fin gates.length) (c : ℕ), (gates.get a).op = PEqualNP.CircuitLowerBounds.GateOp.and → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, N + (a : ℕ)⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0))) = false →
      c ∈ (gates.get a).inputs → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, c⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0))) = false →
      ∀ r ∈ L i0 \ T0, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, N + (a : ℕ)⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0 ∨ v = r))) = true → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, c⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0 ∨ v = r))) = true) := by
  intro q m N L i0 T0 _ _ _ _ _ _ _ _ _ gates u hops hwf hu
  have hwf' : ∀ i : Fin gates.length, ∀ a ∈ (gates.get i).inputs, a < N + (i : ℕ) :=
    fun i => (hwf i).2
  have hops' : ∀ g ∈ gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
      g.op = PEqualNP.CircuitLowerBounds.GateOp.or := fun g hg => (hops g hg).1
  have hlen0 : (List.ofFn (fun v : Fin N => decide (v ∉ L i0))).length = N := List.length_ofFn
  have part1 : ∀ Y : ℕ, PEqualNP.Outside.L_meta_1586.Top gates N u Y →
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, Y⟩
        (List.ofFn (fun v : Fin N => decide (v ∉ L i0))) = false :=
    fun Y hY => PEqualNP.Outside.L_meta_1586.top_false gates N u _ hlen0 hwf' hu Y hY
  have part2 : ∀ p : Fin N, PEqualNP.Outside.L_meta_1586.Top gates N u (p : ℕ) → p ∈ L i0 := by
    intro p hp
    have h := part1 p hp
    rw [PEqualNP.Outside.L_meta_1586.eval_eq,
      PEqualNP.Outside.L_meta_1586.val_input _ _ _ (by rw [hlen0]; exact p.2),
      PEqualNP.Outside.L_meta_1586.getD_ofFn _ _ p.2] at h
    simpa using h
  refine ⟨part1, part2, ?_, ?_⟩
  · intro r _ hr
    have hlenr : (List.ofFn (fun v : Fin N => decide (v ∉ L i0 ∨ v = r))).length = N :=
      List.length_ofFn
    refine PEqualNP.Outside.L_meta_1586.top_rim gates N u (r : ℕ) _ hlenr hops' hwf' ?_ u
      (fun S hS _ => hS) hr
    intro Y hYN hY hv
    rw [PEqualNP.Outside.L_meta_1586.getD_ofFn _ _ hYN] at hv
    have hmem := part2 ⟨Y, hYN⟩ hY
    simp only [decide_eq_true_eq] at hv
    rcases hv with hv | hv
    · exact absurd hmem hv
    · rw [← hv]
  · intro a c hand _ hc _ r _ hr
    have hlenr : (List.ofFn (fun v : Fin N => decide (v ∉ L i0 ∨ v = r))).length = N :=
      List.length_ofFn
    exact PEqualNP.Outside.L_meta_1586.and_input gates N _ hlenr hwf' a hand hr c hc
