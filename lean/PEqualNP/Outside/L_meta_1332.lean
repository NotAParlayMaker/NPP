import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1332_aux

open PEqualNP.CircuitLowerBounds

def T (p N : ℕ) (g : Gate) : Gate :=
  match g.op with
  | GateOp.and => if p ∈ g.inputs then ⟨GateOp.or, []⟩ else g
  | GateOp.or => ⟨GateOp.or, g.inputs.filter (fun i => i ≠ p)⟩
  | _ => ⟨g.op, g.inputs.map (fun i => if i = p then N else i)⟩

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem gv (p N : ℕ) (g : Gate) (r1 r2 : ℕ → Bool) (hN : r1 N = false) (hp : r2 p = false)
    (he : ∀ i, i ≠ p → r1 i = r2 i) :
    (T p N g).op.eval ((T p N g).inputs.map r1) = g.op.eval (g.inputs.map r2) := by
  have hf : ∀ i, r1 (if i = p then N else i) = r2 i := by
    intro i
    split_ifs with h
    · subst h; rw [hN, hp]
    · exact he i h
  obtain ⟨op, ins⟩ := g
  cases op with
  | and =>
    by_cases hm : p ∈ ins
    · simp [T, hm, GateOp.eval]
      exact ⟨p, hm, hp⟩
    · simp only [T, hm, ite_false, GateOp.eval]
      congr 1
      apply List.map_congr_left
      intro i hi
      exact he i (fun h => hm (h ▸ hi))
  | or =>
    simp only [T, GateOp.eval, List.any_map]
    rw [Bool.eq_iff_iff]
    simp only [List.any_eq_true, List.mem_filter, Function.comp, id]
    constructor
    · rintro ⟨i, ⟨hi, hne⟩, h⟩
      exact ⟨i, hi, by rw [← he i (by simpa using hne)]; exact h⟩
    · rintro ⟨i, hi, h⟩
      have hne : i ≠ p := by rintro rfl; rw [hp] at h; exact absurd h (by simp)
      exact ⟨i, ⟨hi, by simpa using hne⟩, by rw [he i hne]; exact h⟩
  | not =>
    simp only [T, List.map_map]
    congr 2
    funext i
    exact hf i
  | mod m =>
    simp only [T, List.map_map]
    congr 2
    funext i
    exact hf i
  | maj =>
    simp only [T, List.map_map]
    congr 2
    funext i
    exact hf i

theorem fold (p N : ℕ) : ∀ (gs : List Gate) (w1 w2 : List Bool), w1.length = w2.length →
    w1.length + gs.length ≤ N → p < w2.length → w2.getD p false = false →
    (∀ i, i ≠ p → w1.getD i false = w2.getD i false) →
    ((gs.map (T p N)).foldl step w1).length = w1.length + gs.length ∧
    (gs.foldl step w2).length = w1.length + gs.length ∧
    (gs.foldl step w2).getD p false = false ∧
    ∀ i, i ≠ p → ((gs.map (T p N)).foldl step w1).getD i false = (gs.foldl step w2).getD i false := by
  intro gs
  induction gs with
  | nil =>
    intro w1 w2 hl _ _ hp he
    refine ⟨by simp, by simp [hl], by simpa using hp, fun i hi => by simpa using he i hi⟩
  | cons g gs ih =>
    intro w1 w2 hl hN hpl hp he
    simp only [List.map_cons, List.foldl_cons]
    have hv : (T p N g).op.eval ((T p N g).inputs.map fun i => w1.getD i false) =
        g.op.eval (g.inputs.map fun i => w2.getD i false) := by
      apply gv p N g _ _ _ hp he
      apply List.getD_eq_default
      simp at hN; omega
    have key := ih (step w1 (T p N g)) (step w2 g) (by simp [step, hl])
      (by simp [step] at hN ⊢; omega) (by simp [step]; omega)
      (by simp only [step]; rw [List.getD_append _ _ _ _ hpl]; exact hp)
      (by
        intro i hi
        simp only [step]
        rcases lt_trichotomy i w1.length with h | h | h
        · rw [List.getD_append _ _ _ _ h, List.getD_append _ _ _ _ (hl ▸ h)]
          exact he i hi
        · subst h
          rw [List.getD_append_right _ _ _ _ (le_refl _), hl, List.getD_append_right _ _ _ _ (le_refl _)]
          simpa using hv
        · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)])
    obtain ⟨k1, k2, k3, k4⟩ := key
    refine ⟨?_, ?_, k3, k4⟩
    · rw [k1]; simp [step]; omega
    · rw [k2]; simp [step]; omega

theorem tk (p N : ℕ) (g : Gate) (h : (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2) :
    ((T p N g).op = GateOp.and ∨ (T p N g).op = GateOp.or ∨ (T p N g).op = GateOp.not) ∧ (T p N g).inputs.length ≤ 2 := by
  obtain ⟨op, ins⟩ := g
  obtain ⟨h1, h2⟩ := h
  cases op <;> simp at h1
  · by_cases hm : p ∈ ins <;> simp [T, hm] <;> simpa using h2
  · simp [T]
    exact le_trans (List.length_filter_le _ _) h2
  · simp [T]
    simpa using h2

theorem tn (p N : ℕ) (g : Gate) (h : (T p N g).op = GateOp.not) : g.op = GateOp.not := by
  obtain ⟨op, ins⟩ := g
  cases op with
  | and => by_cases hm : p ∈ ins <;> simp [T, hm] at h
  | or => simp [T] at h
  | _ => simpa [T] using h

theorem tb (p N : ℕ) (g : Gate) (h2 : g.inputs.length ≤ 2)
    (h : ((T p N g).op = GateOp.and ∨ (T p N g).op = GateOp.or) ∧ (T p N g).inputs.length = 2) :
    ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∧ p ∉ g.inputs := by
  obtain ⟨op, ins⟩ := g
  obtain ⟨h1, h3⟩ := h
  cases op with
  | and =>
    by_cases hm : p ∈ ins
    · simp [T, hm] at h3
    · simp_all [T]
  | or =>
    simp only [T] at h3
    have hle := List.length_filter_le (fun i => decide (i ≠ p)) ins
    have h2' : ins.length ≤ 2 := h2
    refine ⟨⟨Or.inr rfl, by simp; omega⟩, ?_⟩
    intro hm
    have hlt : (List.filter (fun i => decide (i ≠ p)) ins).length < ins.length :=
      List.length_filter_lt_length_iff_exists.mpr ⟨p, hm, by simp⟩
    omega
  | _ => simp [T] at h1

end PEqualNP.Outside.L_meta_1332_aux

open PEqualNP.Outside.L_meta_1332_aux in
theorem PEqualNP.Outside.L_meta_1332 : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)), (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ (o : Fin m) (x : Fin n → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out o⟩ (List.ofFn x) = decide (∃ v ∈ S o, x v = true)) → ∀ p : Fin n, (∃ i0 : Fin m, p ∈ S i0 ∧ ∃ v0 ∈ S i0, v0 ≠ p) → ∀ a b : Fin gates.length, a ≠ b → ((gates.get a).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ (gates.get a).op = PEqualNP.CircuitLowerBounds.GateOp.or) → (gates.get a).inputs.length = 2 → p.val ∈ (gates.get a).inputs → ((gates.get b).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ (gates.get b).op = PEqualNP.CircuitLowerBounds.GateOp.or) → (gates.get b).inputs.length = 2 → p.val ∈ (gates.get b).inputs → ∀ (t : ℕ) (ι : Fin t → Fin gates.length), (∀ q : Fin gates.length, (gates.get q).op = PEqualNP.CircuitLowerBounds.GateOp.not → ∃ r : Fin t, ι r = q) → ∀ I : Finset (Fin gates.length), (∀ q2 : Fin gates.length, ((gates.get q2).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ (gates.get q2).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ (gates.get q2).inputs.length = 2 → q2 ∈ I) → ∃ (gl : List PEqualNP.CircuitLowerBounds.Gate) (ol : Fin m → ℕ) (κ : Fin t → Fin gl.length) (J : Finset (Fin gl.length)), (∀ h ∈ gl, (h.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ h.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ h.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ h.inputs.length ≤ 2) ∧ (∀ q3 : Fin gl.length, (gl.get q3).op = PEqualNP.CircuitLowerBounds.GateOp.not → ∃ r2 : Fin t, κ r2 = q3) ∧ (∀ q4 : Fin gl.length, ((gl.get q4).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ (gl.get q4).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ (gl.get q4).inputs.length = 2 → q4 ∈ J) ∧ J.card + 2 ≤ I.card ∧ ∀ (o2 : Fin m) (x2 : Fin n → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gl, ol o2⟩ (List.ofFn x2) = decide (∃ v2 ∈ S o2, v2 ≠ p ∧ x2 v2 = true) := by
  intro n m S _ gates out hg hev p _ a b hab ha ha2 hpa hb hb2 hpb t ι hι I hI
  have hlen : (gates.map (T p.val (n + gates.length))).length = gates.length := by simp
  have hget : ∀ q : Fin (gates.map (T p.val (n + gates.length))).length,
      (gates.map (T p.val (n + gates.length))).get q = T p.val (n + gates.length) (gates.get (Fin.cast hlen q)) := by
    intro q
    simp
  have haI : a ∈ I := hI a ⟨ha, ha2⟩
  have hbI : b ∈ I.erase a := Finset.mem_erase.mpr ⟨fun h => hab h.symm, hI b ⟨hb, hb2⟩⟩
  refine ⟨gates.map (T p.val (n + gates.length)), fun o => if out o = p.val then n + gates.length else out o,
    fun r => Fin.cast hlen.symm (ι r), ((I.erase a).erase b).map (finCongr hlen.symm).toEmbedding, ?_, ?_, ?_, ?_, ?_⟩
  · intro h hh
    obtain ⟨g, hgm, rfl⟩ := List.mem_map.mp hh
    exact tk _ _ g (hg g hgm)
  · intro q3 hq
    rw [hget] at hq
    obtain ⟨r, hr⟩ := hι _ (tn _ _ _ hq)
    exact ⟨r, by ext; simp [hr]⟩
  · intro q4 hq
    rw [hget] at hq
    have hq2 := tb _ _ _ (hg _ (List.get_mem _ _)).2 hq
    have hqa : Fin.cast hlen q4 ≠ a := by
      intro h
      rw [h] at hq2
      exact hq2.2 hpa
    have hqb : Fin.cast hlen q4 ≠ b := by
      intro h
      rw [h] at hq2
      exact hq2.2 hpb
    rw [Finset.mem_map]
    refine ⟨Fin.cast hlen q4, Finset.mem_erase.mpr ⟨hqb, Finset.mem_erase.mpr ⟨hqa, hI _ hq2.1⟩⟩, ?_⟩
    ext
    simp
  · rw [Finset.card_map, Finset.card_erase_of_mem hbI, Finset.card_erase_of_mem haI]
    have := Finset.card_pos.mpr ⟨b, hbI⟩
    rw [Finset.card_erase_of_mem haI] at this
    omega
  · intro o x2
    have h0 := hev o (fun v => if v = p then false else x2 v)
    unfold PEqualNP.CircuitLowerBounds.Circuit.eval PEqualNP.CircuitLowerBounds.Circuit.wires at h0 ⊢
    change (List.foldl step _ _).getD _ false = _ at h0
    change (List.foldl step _ _).getD _ false = _
    obtain ⟨k1, k2, k3, k4⟩ := fold p.val (n + gates.length) gates (List.ofFn x2)
      (List.ofFn (fun v => if v = p then false else x2 v)) (by simp) (by simp) (by simp)
      (by simp [List.getD_eq_getElem?_getD])
      (by
        intro i hi
        simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
        by_cases hin : i < n
        · simp_all [Fin.ext_iff]
        · simp [hin])
    have hr : decide (∃ v ∈ S o, (if v = p then false else x2 v) = true) = decide (∃ v2 ∈ S o, v2 ≠ p ∧ x2 v2 = true) := by
      simp
    rw [← hr, ← h0]
    simp only
    split_ifs with ho
    · rw [ho, k3, List.getD_eq_default]
      rw [k1]
      simp
    · exact k4 _ ho
