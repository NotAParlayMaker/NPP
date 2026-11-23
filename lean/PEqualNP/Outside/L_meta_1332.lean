import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1332

open PEqualNP.CircuitLowerBounds

def rewGate (p : ℕ) (g : Gate) : Gate :=
  match g.op, g.inputs with
  | GateOp.and, [] => ⟨GateOp.and, []⟩
  | GateOp.and, [u] => if u = p then ⟨GateOp.or, []⟩ else ⟨GateOp.and, [u]⟩
  | GateOp.and, [u, v] => if u = p ∨ v = p then ⟨GateOp.or, []⟩ else ⟨GateOp.and, [u, v]⟩
  | GateOp.or, [] => ⟨GateOp.or, []⟩
  | GateOp.or, [u] => if u = p then ⟨GateOp.or, []⟩ else ⟨GateOp.or, [u]⟩
  | GateOp.or, [u, v] =>
      if u = p then
        if v = p then ⟨GateOp.or, []⟩ else ⟨GateOp.or, [v]⟩
      else
        if v = p then ⟨GateOp.or, [u]⟩ else ⟨GateOp.or, [u, v]⟩
  | GateOp.not, [] => ⟨GateOp.and, []⟩
  | GateOp.not, u :: _ => if u = p then ⟨GateOp.and, []⟩ else ⟨GateOp.not, [u]⟩
  | _, _ => ⟨GateOp.or, []⟩

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def run (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl step w

lemma run_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    run (g :: gs) w = run gs (step w g) := rfl

lemma run_length (gs : List Gate) (w : List Bool) :
    (run gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [run]
  | cons g gs ih =>
    rw [run_cons, ih]
    simp [step]
    omega

lemma getD_append_left_lt (w t : List Bool) (i : ℕ) (hi : i < w.length) :
    (w ++ t).getD i false = w.getD i false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_snoc_eq (w : List Bool) (b : Bool) :
    (w ++ [b]).getD w.length false = b := by
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (le_refl w.length)]
  simp

lemma getD_snoc_ne (w : List Bool) (b : Bool) (i : ℕ) (hi : i ≠ w.length) :
    (w ++ [b]).getD i false = w.getD i false := by
  by_cases hlt : i < w.length
  · exact getD_append_left_lt w [b] i hlt
  · have hge : w.length + 1 ≤ i := by omega
    rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

lemma rewGate_ok (p : ℕ) (g : Gate)
    (hg : (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2) :
    ((rewGate p g).op = GateOp.and ∨ (rewGate p g).op = GateOp.or ∨ (rewGate p g).op = GateOp.not) ∧
      (rewGate p g).inputs.length ≤ 2 := by
  obtain ⟨op, ins⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  simp only at hop hlen
  rcases hop with rfl | rfl | rfl
  · match ins, hlen with
    | [], _ => simp [rewGate]
    | [u], _ => by_cases hu : u = p <;> simp [rewGate, hu]
    | [u, v], _ => by_cases huv : u = p ∨ v = p <;> simp [rewGate, huv]
    | _ :: _ :: _ :: _, h => simp at h
  · match ins, hlen with
    | [], _ => simp [rewGate]
    | [u], _ => by_cases hu : u = p <;> simp [rewGate, hu]
    | [u, v], _ =>
      by_cases hu : u = p <;> by_cases hv : v = p <;> simp [rewGate, hu, hv]
    | _ :: _ :: _ :: _, h => simp at h
  · cases ins with
    | nil => simp [rewGate]
    | cons u rest => by_cases hu : u = p <;> simp [rewGate, hu]

lemma rewGate_not_imp (p : ℕ) (g : Gate)
    (hg : (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (hn : (rewGate p g).op = GateOp.not) : g.op = GateOp.not := by
  obtain ⟨op, ins⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  simp only at hop hlen ⊢
  rcases hop with rfl | rfl | rfl
  · match ins, hlen with
    | [], _ => simp [rewGate] at hn
    | [u], _ => by_cases hu : u = p <;> simp [rewGate, hu] at hn
    | [u, v], _ => by_cases huv : u = p ∨ v = p <;> simp [rewGate, huv] at hn
    | _ :: _ :: _ :: _, h => simp at h
  · match ins, hlen with
    | [], _ => simp [rewGate] at hn
    | [u], _ => by_cases hu : u = p <;> simp [rewGate, hu] at hn
    | [u, v], _ => by_cases hu : u = p <;> by_cases hv : v = p <;> simp [rewGate, hu, hv] at hn
    | _ :: _ :: _ :: _, h => simp at h
  · rfl

lemma rewGate_two_imp (p : ℕ) (g : Gate)
    (hg : (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (htwo : ((rewGate p g).op = GateOp.and ∨ (rewGate p g).op = GateOp.or) ∧
      (rewGate p g).inputs.length = 2) :
    ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∧ p ∉ g.inputs := by
  obtain ⟨op, ins⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  simp only at hop hlen ⊢
  rcases hop with rfl | rfl | rfl
  · match ins, hlen with
    | [], _ => simp [rewGate] at htwo
    | [u], _ => by_cases hu : u = p <;> simp [rewGate, hu] at htwo
    | [u, v], _ =>
      by_cases huv : u = p ∨ v = p
      · simp [rewGate, huv] at htwo
      · push_neg at huv
        refine ⟨⟨Or.inl rfl, rfl⟩, ?_⟩
        simp [Ne.symm huv.1, Ne.symm huv.2]
    | _ :: _ :: _ :: _, h => simp at h
  · match ins, hlen with
    | [], _ => simp [rewGate] at htwo
    | [u], _ => by_cases hu : u = p <;> simp [rewGate, hu] at htwo
    | [u, v], _ =>
      by_cases hu : u = p
      · by_cases hv : v = p <;> simp [rewGate, hu, hv] at htwo
      · by_cases hv : v = p
        · simp [rewGate, hu, hv] at htwo
        · refine ⟨⟨Or.inr rfl, rfl⟩, ?_⟩
          simp [Ne.symm hu, Ne.symm hv]
    | _ :: _ :: _ :: _, h => simp at h
  · cases ins with
    | nil => simp [rewGate] at htwo
    | cons u rest => by_cases hu : u = p <;> simp [rewGate, hu] at htwo

lemma rewGate_eval (p : ℕ) (g : Gate)
    (hg : (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (w w' : List Bool)
    (hwp : w'.getD p false = false)
    (hag : ∀ i : ℕ, i ≠ p → w.getD i false = w'.getD i false) :
    (rewGate p g).op.eval ((rewGate p g).inputs.map fun i => w.getD i false) =
      g.op.eval (g.inputs.map fun i => w'.getD i false) := by
  simp only [List.getD_eq_getElem?_getD] at hwp hag
  obtain ⟨op, ins⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  simp only at hop hlen
  rcases hop with rfl | rfl | rfl
  · match ins, hlen with
    | [], _ => rfl
    | [u], _ =>
      by_cases hu : u = p
      · subst u; simp [rewGate, GateOp.eval, hwp]
      · simp [rewGate, hu, GateOp.eval, hag u hu]
    | [u, v], _ =>
      by_cases hu : u = p
      · subst u; simp [rewGate, GateOp.eval, hwp]
      · by_cases hv : v = p
        · subst v; simp [rewGate, hu, GateOp.eval, hwp]
        · simp [rewGate, hu, hv, GateOp.eval, hag u hu, hag v hv]
    | _ :: _ :: _ :: _, h => simp at h
  · match ins, hlen with
    | [], _ => rfl
    | [u], _ =>
      by_cases hu : u = p
      · subst u; simp [rewGate, GateOp.eval, hwp]
      · simp [rewGate, hu, GateOp.eval, hag u hu]
    | [u, v], _ =>
      by_cases hu : u = p
      · by_cases hv : v = p
        · subst u; subst v; simp [rewGate, GateOp.eval, hwp]
        · subst u; simp [rewGate, hv, GateOp.eval, hwp, hag v hv]
      · by_cases hv : v = p
        · subst v; simp [rewGate, hu, GateOp.eval, hwp, hag u hu]
        · simp [rewGate, hu, hv, GateOp.eval, hag u hu, hag v hv]
    | _ :: _ :: _ :: _, h => simp at h
  · cases ins with
    | nil => simp [rewGate, GateOp.eval]
    | cons u rest =>
      by_cases hu : u = p
      · subst u; simp [rewGate, GateOp.eval, hwp]
      · simp [rewGate, hu, GateOp.eval, hag u hu]

lemma run_rew (p : ℕ) (gs : List Gate)
    (hgs : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2) :
    ∀ w w' : List Bool,
      w.length = w'.length →
      p < w'.length →
      w'.getD p false = false →
      (∀ i : ℕ, i ≠ p → w.getD i false = w'.getD i false) →
      (run (gs.map (rewGate p)) w).length = (run gs w').length ∧
      (run gs w').getD p false = false ∧
      ∀ i : ℕ, i ≠ p → (run (gs.map (rewGate p)) w).getD i false = (run gs w').getD i false := by
  induction gs with
  | nil =>
    intro w w' hlen _ hwp hag
    exact ⟨hlen, hwp, hag⟩
  | cons g gs ih =>
    intro w w' hlen hpl hwp hag
    have hg := hgs g List.mem_cons_self
    have hgs' : ∀ g' ∈ gs,
        (g'.op = GateOp.and ∨ g'.op = GateOp.or ∨ g'.op = GateOp.not) ∧ g'.inputs.length ≤ 2 :=
      fun g' hg' => hgs g' (List.mem_cons_of_mem g hg')
    simp only [List.map_cons, run_cons]
    apply ih hgs' (step w (rewGate p g)) (step w' g)
    · simp [step, hlen]
    · simp [step]; omega
    · simp only [step]
      rw [getD_append_left_lt w' _ p hpl, hwp]
    · intro i hi
      simp only [step]
      by_cases hil : i = w.length
      · subst hil
        rw [getD_snoc_eq, hlen, getD_snoc_eq]
        exact rewGate_eval p g hg w w' hwp hag
      · rw [getD_snoc_ne w _ i hil, getD_snoc_ne w' _ i (by omega)]
        exact hag i hi

end PEqualNP.Outside.L_meta_1332

open PEqualNP.Outside.L_meta_1332 in
theorem PEqualNP.Outside.L_meta_1332 : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)), (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ (o : Fin m) (x : Fin n → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out o⟩ (List.ofFn x) = decide (∃ v ∈ S o, x v = true)) → ∀ p : Fin n, (∃ i0 : Fin m, p ∈ S i0 ∧ ∃ v0 ∈ S i0, v0 ≠ p) → ∀ a b : Fin gates.length, a ≠ b → ((gates.get a).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ (gates.get a).op = PEqualNP.CircuitLowerBounds.GateOp.or) → (gates.get a).inputs.length = 2 → p.val ∈ (gates.get a).inputs → ((gates.get b).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ (gates.get b).op = PEqualNP.CircuitLowerBounds.GateOp.or) → (gates.get b).inputs.length = 2 → p.val ∈ (gates.get b).inputs → ∀ (t : ℕ) (ι : Fin t → Fin gates.length), (∀ q : Fin gates.length, (gates.get q).op = PEqualNP.CircuitLowerBounds.GateOp.not → ∃ r : Fin t, ι r = q) → ∀ I : Finset (Fin gates.length), (∀ q2 : Fin gates.length, ((gates.get q2).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ (gates.get q2).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ (gates.get q2).inputs.length = 2 → q2 ∈ I) → ∃ (gl : List PEqualNP.CircuitLowerBounds.Gate) (ol : Fin m → ℕ) (κ : Fin t → Fin gl.length) (J : Finset (Fin gl.length)), (∀ h ∈ gl, (h.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ h.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ h.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ h.inputs.length ≤ 2) ∧ (∀ q3 : Fin gl.length, (gl.get q3).op = PEqualNP.CircuitLowerBounds.GateOp.not → ∃ r2 : Fin t, κ r2 = q3) ∧ (∀ q4 : Fin gl.length, ((gl.get q4).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ (gl.get q4).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ (gl.get q4).inputs.length = 2 → q4 ∈ J) ∧ J.card + 2 ≤ I.card ∧ ∀ (o2 : Fin m) (x2 : Fin n → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gl, ol o2⟩ (List.ofFn x2) = decide (∃ v2 ∈ S o2, v2 ≠ p ∧ x2 v2 = true) := by
  classical
  intro n m S _ gates out hG heval p _ a b hab ha_op ha_len ha_mem hb_op hb_len hb_mem t ι hnot I hI
  let gl := gates.map (rewGate p.val)
  have hlen : gl.length = gates.length := List.length_map _
  let ol : Fin m → ℕ := fun o2 => if out o2 = p.val then n + gates.length else out o2
  let e : Fin gates.length ≃ Fin gl.length := finCongr hlen.symm
  let κ : Fin t → Fin gl.length := fun r => e (ι r)
  let J : Finset (Fin gl.length) := ((I.erase a).erase b).map e.toEmbedding
  refine ⟨gl, ol, κ, J, ?_, ?_, ?_, ?_, ?_⟩
  · intro h hh
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hh
    exact rewGate_ok p.val g (hG g hg)
  · intro q3 hq3
    let q3' : Fin gates.length := e.symm q3
    have hget : gl.get q3 = rewGate p.val (gates.get q3') := by
      simp [gl, q3', e]
    rw [hget] at hq3
    have hgn : (gates.get q3').op = PEqualNP.CircuitLowerBounds.GateOp.not :=
      rewGate_not_imp p.val (gates.get q3') (hG _ (List.get_mem _ _)) hq3
    obtain ⟨r2, hr2⟩ := hnot q3' hgn
    refine ⟨r2, ?_⟩
    simp [κ, hr2, q3']
  · intro q4 hq4
    let q4' : Fin gates.length := e.symm q4
    have hget : gl.get q4 = rewGate p.val (gates.get q4') := by
      simp [gl, q4', e]
    rw [hget] at hq4
    obtain ⟨hq4_two, hq4_notmem⟩ := rewGate_two_imp p.val (gates.get q4') (hG _ (List.get_mem _ _)) hq4
    have hmemI : q4' ∈ I := hI q4' hq4_two
    have hnea : q4' ≠ a := fun h => hq4_notmem (h ▸ ha_mem)
    have hneb : q4' ≠ b := fun h => hq4_notmem (h ▸ hb_mem)
    have hmem : q4' ∈ (I.erase a).erase b :=
      Finset.mem_erase.mpr ⟨hneb, Finset.mem_erase.mpr ⟨hnea, hmemI⟩⟩
    exact Finset.mem_map.mpr ⟨q4', hmem, by simp [q4']⟩
  · have haI : a ∈ I := hI a ⟨ha_op, ha_len⟩
    have hbI : b ∈ I := hI b ⟨hb_op, hb_len⟩
    have hbIa : b ∈ I.erase a := Finset.mem_erase.mpr ⟨Ne.symm hab, hbI⟩
    have hcardJ : J.card = ((I.erase a).erase b).card := Finset.card_map _
    have h1 := Finset.card_erase_add_one hbIa
    have h2 := Finset.card_erase_add_one haI
    omega
  · intro o2 x2
    let x' : Fin n → Bool := fun v => if v = p then false else x2 v
    have hrun := run_rew p.val gates hG (List.ofFn x2) (List.ofFn x')
      (by simp) (by simp)
      (by
        rw [List.getD_eq_getElem _ _ (by simp)]
        simp [x'])
      (by
        intro i hi
        by_cases hin : i < n
        · rw [List.getD_eq_getElem _ _ (by simp [hin]), List.getD_eq_getElem _ _ (by simp [hin])]
          simp only [List.getElem_ofFn, x']
          have hne : (⟨i, hin⟩ : Fin n) ≠ p := fun h => hi (congrArg Fin.val h)
          simp [hne]
        · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)])
    obtain ⟨hrlen, hrp, hrag⟩ := hrun
    have hev : PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gl, ol o2⟩ (List.ofFn x2) =
        PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out o2⟩ (List.ofFn x') := by
      change (run gl (List.ofFn x2)).getD (ol o2) false = (run gates (List.ofFn x')).getD (out o2) false
      by_cases ho : out o2 = p.val
      · simp only [ol, ho, ite_true]
        rw [List.getD_eq_default _ _ (by rw [run_length]; simp [gl]), hrp]
      · simp only [ol, ho, ite_false]
        exact hrag (out o2) ho
    rw [hev, heval o2 x']
    simp only [decide_eq_decide, x']
    constructor
    · rintro ⟨v2, hv2, hx⟩
      by_cases hvp : v2 = p
      · simp [hvp] at hx
      · simp [hvp] at hx
        exact ⟨v2, hv2, hvp, hx⟩
    · rintro ⟨v2, hv2, hvp, hx⟩
      exact ⟨v2, hv2, by simp [hvp, hx]⟩
