import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1332_aux

open PEqualNP.CircuitLowerBounds

/-- Set wire `p` to false inside one gate. -/
def f (p : ℕ) (g : Gate) : Gate :=
  match g.op with
  | GateOp.or => ⟨GateOp.or, g.inputs.filter (fun i => decide (i ≠ p))⟩
  | GateOp.and => if p ∈ g.inputs then ⟨GateOp.or, []⟩ else g
  | GateOp.not => if g.inputs.head? = some p then ⟨GateOp.and, []⟩ else g
  | _ => g

def Ok (g : Gate) : Prop :=
  (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2

def run (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem gate_eq (p : ℕ) (w w' : List Bool)
    (hag : ∀ i, i ≠ p → w.getD i false = w'.getD i false) (hp : w'.getD p false = false)
    (g : Gate) (hg : Ok g) :
    (f p g).op.eval ((f p g).inputs.map fun i => w.getD i false) =
      g.op.eval (g.inputs.map fun i => w'.getD i false) := by
  obtain ⟨op, ins⟩ := g
  obtain ⟨hop, -⟩ := hg
  cases op with
  | or =>
    simp only [f, GateOp.eval]
    clear hop
    induction ins with
    | nil => rfl
    | cons i t ih =>
      by_cases h : i = p
      · subst h
        simp only [List.filter_cons, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true,
          if_false, List.map_cons, List.any_cons, id, hp, Bool.false_or]
        exact ih
      · simp only [List.filter_cons, ne_eq, h, not_false_eq_true, decide_true, if_true,
          List.map_cons, List.any_cons, id, hag i h]
        rw [ih]
  | and =>
    simp only [f]
    by_cases h : p ∈ ins
    · simp only [h, if_true, GateOp.eval, List.map_nil, List.any_nil]
      symm
      rw [List.all_eq_false]
      exact ⟨w'.getD p false, List.mem_map.2 ⟨p, h, rfl⟩, by simp only [id, hp]; simp⟩
    · simp only [h, if_false]
      congr 1
      apply List.map_congr_left
      intro i hi
      exact hag i (fun e => h (e ▸ hi))
  | not =>
    simp only [f]
    cases ins with
    | nil => simp
    | cons i t =>
      by_cases h : i = p
      · subst h
        simp only [List.head?_cons, ↓reduceIte, GateOp.eval, List.map_cons, List.headD_cons, hp]
        rfl
      · have h' : ¬ (some i = some p) := fun e => h (Option.some.inj e)
        simp only [List.head?_cons, h', if_false, GateOp.eval, List.map_cons, List.headD_cons,
          hag i h]
  | mod m => simp at hop
  | maj => simp at hop

theorem run_length (gs : List Gate) (w : List Bool) : (run gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => rfl
  | cons g t ih =>
    simp only [run, List.foldl_cons] at ih ⊢
    rw [ih]
    simp
    omega

theorem run_agree (p : ℕ) (gs : List Gate) (hgs : ∀ g ∈ gs, Ok g) (w w' : List Bool)
    (hlen : w.length = w'.length) (hlt : p < w'.length)
    (hag : ∀ i, i ≠ p → w.getD i false = w'.getD i false) (hp : w'.getD p false = false) :
    (∀ i, i ≠ p → (run (gs.map (f p)) w).getD i false = (run gs w').getD i false) ∧
      (run gs w').getD p false = false := by
  induction gs generalizing w w' with
  | nil => exact ⟨hag, hp⟩
  | cons g t ih =>
    simp only [run, List.map_cons, List.foldl_cons]
    rw [gate_eq p w w' hag hp g (hgs g (by simp))]
    apply ih (fun g' hg' => hgs g' (by simp [hg']))
    · simp [hlen]
    · simp; omega
    · intro i hi
      have := hag i hi
      simp only [List.getD_eq_getElem?_getD] at this ⊢
      simp only [List.getElem?_append, hlen]
      split
      · exact this
      · rfl
    · simp only [List.getD_eq_getElem?_getD] at hp ⊢
      rw [List.getElem?_append_left hlt]
      exact hp

end PEqualNP.Outside.L_meta_1332_aux

open PEqualNP.Outside.L_meta_1332_aux PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_1332 : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)), (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ (o : Fin m) (x : Fin n → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out o⟩ (List.ofFn x) = decide (∃ v ∈ S o, x v = true)) → ∀ p : Fin n, (∃ i0 : Fin m, p ∈ S i0 ∧ ∃ v0 ∈ S i0, v0 ≠ p) → ∀ a b : Fin gates.length, a ≠ b → ((gates.get a).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ (gates.get a).op = PEqualNP.CircuitLowerBounds.GateOp.or) → (gates.get a).inputs.length = 2 → p.val ∈ (gates.get a).inputs → ((gates.get b).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ (gates.get b).op = PEqualNP.CircuitLowerBounds.GateOp.or) → (gates.get b).inputs.length = 2 → p.val ∈ (gates.get b).inputs → ∀ (t : ℕ) (ι : Fin t → Fin gates.length), (∀ q : Fin gates.length, (gates.get q).op = PEqualNP.CircuitLowerBounds.GateOp.not → ∃ r : Fin t, ι r = q) → ∀ I : Finset (Fin gates.length), (∀ q2 : Fin gates.length, ((gates.get q2).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ (gates.get q2).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ (gates.get q2).inputs.length = 2 → q2 ∈ I) → ∃ (gl : List PEqualNP.CircuitLowerBounds.Gate) (ol : Fin m → ℕ) (κ : Fin t → Fin gl.length) (J : Finset (Fin gl.length)), (∀ h ∈ gl, (h.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ h.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ h.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ h.inputs.length ≤ 2) ∧ (∀ q3 : Fin gl.length, (gl.get q3).op = PEqualNP.CircuitLowerBounds.GateOp.not → ∃ r2 : Fin t, κ r2 = q3) ∧ (∀ q4 : Fin gl.length, ((gl.get q4).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ (gl.get q4).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ (gl.get q4).inputs.length = 2 → q4 ∈ J) ∧ J.card + 2 ≤ I.card ∧ ∀ (o2 : Fin m) (x2 : Fin n → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gl, ol o2⟩ (List.ofFn x2) = decide (∃ v2 ∈ S o2, v2 ≠ p ∧ x2 v2 = true) := by
  intro n m S _ gates out hgates hcomp p _ a b hab ha1 ha2 ha3 hb1 hb2 hb3 t ι hι I hI
  have hlen : (gates.map (f p.val)).length = gates.length := List.length_map _
  have hget : ∀ q : Fin (gates.map (f p.val)).length,
      (gates.map (f p.val)).get q = f p.val (gates.get (Fin.cast hlen q)) := by
    intro q
    simp [List.get_eq_getElem]
  refine ⟨gates.map (f p.val), fun o => if out o = p.val then n + gates.length else out o,
    fun r => Fin.cast hlen.symm (ι r),
    ((I.erase a).erase b).map (finCongr hlen.symm).toEmbedding, ?_, ?_, ?_, ?_, ?_⟩
  · intro h hh
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hh
    obtain ⟨hop, hl⟩ := hgates g hg
    obtain ⟨op, ins⟩ := g
    simp only at hop hl
    rcases hop with rfl | rfl | rfl
    · simp only [f]; split <;> simp [hl]
    · simp only [f]
      exact ⟨by simp, le_trans (List.length_filter_le _ _) hl⟩
    · simp only [f]; split <;> simp [hl]
  · intro q hq
    rw [hget] at hq
    have hq' : (gates.get (Fin.cast hlen q)).op = GateOp.not := by
      generalize gates.get (Fin.cast hlen q) = g at hq
      obtain ⟨op, ins⟩ := g
      cases op with
      | not => rfl
      | or => simp [f] at hq
      | and => simp only [f] at hq; split at hq <;> simp at hq
      | mod k => simp [f] at hq
      | maj => simp [f] at hq
    obtain ⟨r, hr⟩ := hι _ hq'
    refine ⟨r, ?_⟩
    show Fin.cast hlen.symm (ι r) = q
    rw [hr]; ext; rfl
  · intro q hq
    rw [hget] at hq
    have key : ((gates.get (Fin.cast hlen q)).op = GateOp.and ∨
        (gates.get (Fin.cast hlen q)).op = GateOp.or) ∧
        (gates.get (Fin.cast hlen q)).inputs.length = 2 ∧
        p.val ∉ (gates.get (Fin.cast hlen q)).inputs := by
      have hle := (hgates _ (List.get_mem gates (Fin.cast hlen q))).2
      generalize gates.get (Fin.cast hlen q) = g at hq hle
      obtain ⟨op, ins⟩ := g
      obtain ⟨hop, hl2⟩ := hq
      cases op with
      | or =>
        simp only [f] at hl2
        have h1 := List.length_filter_le (fun i => decide (i ≠ p.val)) ins
        have h2 : ins.length = 2 := by simp only at hle; omega
        refine ⟨Or.inr rfl, h2, ?_⟩
        intro hmem
        have h3 : (ins.filter (fun i => decide (i ≠ p.val))).length = ins.length := by omega
        have h4 := List.length_filter_eq_length_iff.1 h3 p.val hmem
        simp at h4
      | and =>
        simp only [f] at hl2 hop
        by_cases hmem : p.val ∈ ins
        · simp [hmem] at hl2
        · simp only [hmem, if_false] at hl2
          exact ⟨Or.inl rfl, hl2, hmem⟩
      | not =>
        by_cases hh : ins.head? = some p.val
        · simp [f, hh] at hl2
        · simp [f, hh] at hop
      | mod k => simp [f] at hop
      | maj => simp [f] at hop
    have hI' := hI (Fin.cast hlen q) ⟨key.1, key.2.1⟩
    have hqa : Fin.cast hlen q ≠ a := fun e => key.2.2 (e ▸ ha3)
    have hqb : Fin.cast hlen q ≠ b := fun e => key.2.2 (e ▸ hb3)
    rw [Finset.mem_map]
    exact ⟨Fin.cast hlen q, Finset.mem_erase.2 ⟨hqb, Finset.mem_erase.2 ⟨hqa, hI'⟩⟩, by ext; rfl⟩
  · rw [Finset.card_map]
    have haI : a ∈ I := hI a ⟨ha1, ha2⟩
    have hbI : b ∈ I.erase a := Finset.mem_erase.2 ⟨hab.symm, hI b ⟨hb1, hb2⟩⟩
    have h1 := Finset.card_erase_add_one hbI
    have h2 := Finset.card_erase_add_one haI
    omega
  · intro o x
    have hold := hcomp o (Function.update x p false)
    have hagree := run_agree p.val gates (fun g hg => hgates g hg) (List.ofFn x)
      (List.ofFn (Function.update x p false)) (by simp) (by simp)
      (by
        intro i hi
        simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
        split
        · rename_i hin
          have : (⟨i, hin⟩ : Fin n) ≠ p := fun e => hi (congrArg Fin.val e)
          simp [Function.update_of_ne this]
        · rfl)
      (by simp [List.getD_eq_getElem?_getD])
    have hdec : decide (∃ v ∈ S o, Function.update x p false v = true) =
        decide (∃ v ∈ S o, v ≠ p ∧ x v = true) := by
      apply decide_eq_decide.2
      constructor
      · rintro ⟨v, hv, h⟩
        by_cases hvp : v = p
        · subst hvp; simp at h
        · exact ⟨v, hv, hvp, by rwa [Function.update_of_ne hvp] at h⟩
      · rintro ⟨v, hv, hvp, h⟩
        exact ⟨v, hv, by rwa [Function.update_of_ne hvp]⟩
    rw [← hdec, ← hold]
    change (run (gates.map (f p.val)) (List.ofFn x)).getD
        (if out o = p.val then n + gates.length else out o) false =
      (run gates (List.ofFn (Function.update x p false))).getD (out o) false
    by_cases ho : out o = p.val
    · rw [if_pos ho, ho, hagree.2]
      apply List.getD_eq_default
      rw [run_length]
      simp
    · rw [if_neg ho]
      exact hagree.1 _ ho
