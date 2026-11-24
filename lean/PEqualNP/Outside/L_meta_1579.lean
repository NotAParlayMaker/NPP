import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1579

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map (fun i => w.getD i false))]

def run (gates : List Gate) (x : List Bool) : List Bool := gates.foldl step x

def read (gates : List Gate) (x : List Bool) (i : ℕ) : Bool := (run gates x).getD i false

def Ordered (gates : List Gate) (n : ℕ) : Prop :=
  ∀ i : Fin gates.length, ∀ a ∈ (gates.get i).inputs, a < n + i.val

lemma read_prefix (gates : List Gate) (x : List Bool) (i : ℕ) (h : i < x.length) :
    read gates x i = x.getD i false := by
  induction gates generalizing x with
  | nil => rfl
  | cons g gates ih =>
    change read gates (step x g) i = x.getD i false
    rw [ih (step x g) (by simp [step]; omega)]
    simp [step, List.getD, List.getElem?_append_left h]

lemma read_gate (gates : List Gate) (x : List Bool) (ord : Ordered gates x.length)
    (i : ℕ) (h : i < gates.length) :
    read gates x (x.length + i) = gates[i].op.eval (gates[i].inputs.map (read gates x)) := by
  induction gates generalizing x i with
  | nil => simp at h
  | cons g gates ih =>
    cases i with
    | zero =>
      change read gates (step x g) x.length = g.op.eval (g.inputs.map (read (g :: gates) x))
      rw [read_prefix gates (step x g) x.length (by simp [step])]
      have hstep : (step x g).getD x.length false =
          g.op.eval (g.inputs.map (fun a => x.getD a false)) := by simp [step]
      rw [hstep]
      congr 1
      apply List.map_congr_left
      intro a ha
      have hlt : a < x.length := by
        simpa using ord ⟨0, by simp⟩ a ha
      exact (read_prefix (g :: gates) x a hlt).symm
    | succ i =>
      have hi : i < gates.length := by simpa using h
      change read gates (step x g) (x.length + (i + 1)) =
        gates[i].op.eval (gates[i].inputs.map (read gates (step x g)))
      rw [show x.length + (i + 1) = (step x g).length + i by simp [step]; omega]
      refine ih (step x g) ?_ i hi
      intro j a ha
      have hlt : a < x.length + (j.val + 1) := ord ⟨j.val + 1, by simp⟩ a ha
      simp [step]
      omega

lemma read_input (gates : List Gate) (x : Fin 13 → Bool) (i : Fin 13) :
    read gates (List.ofFn x) i.val = x i := by
  have h : i.val < (List.ofFn x).length := by simp
  rw [read_prefix gates (List.ofFn x) i.val h]
  simp only [List.getD, List.getElem?_eq_getElem h, Option.getD_some, List.getElem_ofFn]

lemma read_gate13 (gates : List Gate) (ord : Ordered gates 13) (x : Fin 13 → Bool)
    (i : Fin gates.length) :
    read gates (List.ofFn x) (13 + i.val) =
      (gates.get i).op.eval ((gates.get i).inputs.map (read gates (List.ofFn x))) := by
  have hw : (List.ofFn x).length = 13 := by simp
  have hordered : Ordered gates (List.ofFn x).length := by simpa only [hw] using ord
  simpa only [hw, List.get_eq_getElem] using
    read_gate gates (List.ofFn x) hordered i.val i.isLt

def Reach (gates : List Gate) (u y : ℕ) : Prop :=
  ∀ S : Set ℕ, u ∈ S → (∀ i : Fin gates.length, 13 + i.val ∈ S →
    (gates.get i).op = GateOp.or → ∀ a ∈ (gates.get i).inputs, a ∈ S) → y ∈ S

def Lit (gates : List Gate) (x : Fin 13 → Bool) (u : ℕ) : Bool :=
  read gates (List.ofFn x) u

lemma descend (gates : List Gate) (ord : Ordered gates 13)
    (ops : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (a b t : Fin 13 → Bool) (noPrimary : ∀ i, a i = false → b i = false → t i ≠ true) :
    ∀ u, u < 13 + gates.length → Lit gates a u = false → Lit gates b u = false →
      Lit gates t u = true → ∃ y, Reach gates u y ∧
        (∃ i : Fin gates.length, y = 13 + i.val ∧ (gates.get i).op = GateOp.and) ∧
        y ≤ u ∧ Lit gates a y = false ∧ Lit gates b y = false ∧ Lit gates t y = true := by
  intro u
  induction u using Nat.strong_induction_on with
  | ind u ih =>
    intro hu ha hb ht
    by_cases hprim : u < 13
    · let i : Fin 13 := ⟨u, hprim⟩
      change Lit gates a i.val = false at ha
      change Lit gates b i.val = false at hb
      change Lit gates t i.val = true at ht
      exact (noPrimary i (by simpa only [Lit, read_input] using ha)
        (by simpa only [Lit, read_input] using hb)
        (by simpa only [Lit, read_input] using ht)).elim
    let i : Fin gates.length := ⟨u - 13, by omega⟩
    have hui : u = 13 + i.val := by dsimp [i]; omega
    rcases (ops (gates.get i) (List.get_mem gates i)).1 with hop | hop
    · exact ⟨u, fun _ hs _ => hs, ⟨i, hui, hop⟩, le_rfl, ha, hb, ht⟩
    have eval_or (x : Fin 13 → Bool) :
        Lit gates x u = true ↔
          ∃ p ∈ (gates.get i).inputs, Lit gates x p = true := by
      unfold Lit
      rw [hui, read_gate13 gates ord, hop]
      simp [GateOp.eval, List.any_eq_true]
    obtain ⟨p, hp, hpTrue⟩ := (eval_or t).1 ht
    have hpLt : p < u := by simpa only [hui] using ord i p hp
    have false_side (x : Fin 13 → Bool) (hx : Lit gates x u = false) : Lit gates x p = false := by
      cases hh : Lit gates x p
      · rfl
      · have := (eval_or x).2 ⟨p, hp, hh⟩
        simp [hx] at this
    obtain ⟨y, reach, andGate, hy, hya, hyb, hyt⟩ :=
      ih p hpLt (by omega) (false_side a ha) (false_side b hb) hpTrue
    refine ⟨y, ?_, andGate, by omega, hya, hyb, hyt⟩
    intro S huS hclosed
    exact reach S (hclosed i (hui ▸ huS) hop p hp) hclosed

lemma excludesOne : ∀ l : Fin 13, l ∈ ({4, 10, 12} : Finset (Fin 13)) →
    1 ∉ ({l, l + 1, l + 3, l + 9} : Finset (Fin 13)) := by decide

lemma excludesZero : ∀ m : Fin 13, m ∈ ({1, 5, 11} : Finset (Fin 13)) →
    0 ∉ ({m, m + 1, m + 3, m + 9} : Finset (Fin 13)) := by decide

lemma test_trace (gates : List Gate) (ord : Ordered gates 13)
    (ops : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (zs : Fin gates.length) (u v : ℕ) (hop : (gates.get zs).op = GateOp.and)
    (hin : (gates.get zs).inputs = [u, v])
    (L M : Finset (Fin 13)) (c p q r : Fin 13) (cross : L ∩ M = {c}) (hpc : p ≠ c)
    (outside : q ∉ L ∨ q ∉ M)
    (hl : Lit gates (fun j => decide (j ∉ L)) u = false)
    (hm : Lit gates (fun j => decide (j ∉ M)) u = false)
    (ht : Lit gates (fun j => decide (j = p ∨ (p ≠ r ∧ j = q))) (13 + zs.val) = true) :
    ∃ y, Reach gates u y ∧
      (∃ i : Fin gates.length, y = 13 + i.val ∧ (gates.get i).op = GateOp.and) ∧
      y < 13 + zs.val ∧ Lit gates (fun j => decide (j ∉ L)) y = false ∧
      Lit gates (fun j => decide (j ∉ M)) y = false ∧
      Lit gates (fun j => decide (j = p ∨ (p ≠ r ∧ j = q))) y = true := by
  let t : Fin 13 → Bool := fun j => decide (j = p ∨ (p ≠ r ∧ j = q))
  have ht' : Lit gates t u = true := by
    change read gates (List.ofFn t) (13 + zs.val) = true at ht
    rw [read_gate13 gates ord, hop, hin] at ht
    have hBoth : read gates (List.ofFn t) u = true ∧ read gates (List.ofFn t) v = true := by
      simpa [GateOp.eval] using ht
    exact hBoth.1
  have noPrimary j : decide (j ∉ L) = false → decide (j ∉ M) = false → t j ≠ true := by
    intro hL hM hT
    have jL : j ∈ L := by simpa using hL
    have jM : j ∈ M := by simpa using hM
    have jCross : j ∈ L ∩ M := Finset.mem_inter.mpr ⟨jL, jM⟩
    have jc : j = c := by simpa [cross] using jCross
    rcases (of_decide_eq_true hT) with rfl | ⟨_, rfl⟩
    · exact hpc jc
    · exact outside.elim (fun h => h jL) (fun h => h jM)
  have hmem : u ∈ (gates.get zs).inputs := by rw [hin]; simp
  have hu : u < 13 + zs.val := ord zs u hmem
  obtain ⟨y, reach, andGate, hy, hya, hyb, hyt⟩ :=
    descend gates ord ops _ _ _ noPrimary u (by omega) hl hm ht'
  exact ⟨y, reach, andGate, by omega, hya, hyb, hyt⟩

end PEqualNP.Outside.L_meta_1579


open PEqualNP.Outside.L_meta_1579

theorem PEqualNP.Outside.L_meta_1579 : ∀ L : Fin 13 → Finset (Fin 13), (∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9}) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (zs : Fin gates.length) (u v : ℕ) (l m c : Fin 13),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ i : Fin gates.length, ∀ a ∈ (gates.get i).inputs, a < 13 + (i : ℕ)) → l ∈ ({4, 10, 12} : Finset (Fin 13)) → m ∈ ({1, 5, 11} : Finset (Fin 13)) → L l ∩ L m = {c} →
    (gates.get zs).op = PEqualNP.CircuitLowerBounds.GateOp.and → (gates.get zs).inputs = [u, v] →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, u⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L l))) = false → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, u⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L m))) = false →
    (∀ p ∈ L l, p ≠ 0 → p ≠ c → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (zs : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v = p ∨ (p ≠ 0 ∧ v = 1)))) = true →
      ∃ Y : ℕ, (∀ S : Set ℕ, u ∈ S → (∀ i : Fin gates.length, 13 + (i : ℕ) ∈ S → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ a ∈ (gates.get i).inputs, a ∈ S) → Y ∈ S) ∧ (∃ i : Fin gates.length, Y = 13 + (i : ℕ) ∧ (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and) ∧ Y < 13 + (zs : ℕ) ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, Y⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L l))) = false ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, Y⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L m))) = false ∧
        PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, Y⟩ (List.ofFn (fun v : Fin 13 => decide (v = p ∨ (p ≠ 0 ∧ v = 1)))) = true) ∧
    (∀ p ∈ L m, p ≠ 1 → p ≠ c → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (zs : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v = p ∨ (p ≠ 1 ∧ v = 0)))) = true →
      ∃ Y : ℕ, (∀ S : Set ℕ, u ∈ S → (∀ i : Fin gates.length, 13 + (i : ℕ) ∈ S → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ a ∈ (gates.get i).inputs, a ∈ S) → Y ∈ S) ∧ (∃ i : Fin gates.length, Y = 13 + (i : ℕ) ∧ (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and) ∧ Y < 13 + (zs : ℕ) ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, Y⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L l))) = false ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, Y⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L m))) = false ∧
        PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, Y⟩ (List.ofFn (fun v : Fin 13 => decide (v = p ∨ (p ≠ 1 ∧ v = 0)))) = true) := by
  intro L hL gates zs u v l m c ops ord hl hm cross hop hin aliveL aliveM
  have hone : 1 ∉ L l := by rw [hL]; exact excludesOne l hl
  have hzero : 0 ∉ L m := by rw [hL]; exact excludesZero m hm
  constructor
  · intro p _ _ hpc ht
    exact test_trace gates ord ops zs u v hop hin (L l) (L m) c p 1 0 cross hpc
      (Or.inl hone) aliveL aliveM ht
  · intro p _ _ hpc ht
    exact test_trace gates ord ops zs u v hop hin (L l) (L m) c p 0 1 cross hpc
      (Or.inr hzero) aliveL aliveM ht
