import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7796

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

theorem run_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    run (gs ++ [g]) x = run gs x ++ [g.op.eval (g.inputs.map fun i => (run gs x).getD i false)] := by
  simp [run, List.foldl_append]

theorem run_length (gs : List Gate) (x : List Bool) : (run gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton gs g ih => rw [run_snoc]; simp [ih]; omega

theorem getD_lt (l : List Bool) (b : Bool) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t false = l.getD t false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_at (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_ltz {α : Type} (z : α) (l : List α) (b : α) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t z = l.getD t z := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_at' {α : Type} (z : α) (l : List α) (b : α) : (l ++ [b]).getD l.length z = b := by
  simp [List.getD_eq_getElem?_getD]

theorem run_prefix (gs hs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length + gs.length) :
    (run (gs ++ hs) x).getD i false = (run gs x).getD i false := by
  induction hs using List.reverseRecOn with
  | nil => simp
  | append_singleton hs g ih =>
    rw [← List.append_assoc, run_snoc, getD_ltz false _ _ _ (by
      rw [run_length, List.length_append]; omega), ih]

theorem run_input (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (run gs x).getD i false = x.getD i false := by
  have := run_prefix [] gs x i (by simpa using hi)
  simpa [run] using this

theorem run_gate (gs : List Gate) (x : List Bool) : ∀ (j : ℕ) (hj : j < gs.length),
    (run gs x).getD (x.length + j) false = gs[j].op.eval (gs[j].inputs.map fun i =>
      if i < x.length + j then (run gs x).getD i false else false) := by
  induction gs using List.reverseRecOn with
  | nil => intro j hj; simp at hj
  | append_singleton gs g ih =>
    intro j hj
    have hlen : (run gs x).length = x.length + gs.length := run_length gs x
    have same : ∀ (k : ℕ), k ≤ gs.length → ∀ l : List ℕ,
        (l.map fun i => if i < x.length + k then (run (gs ++ [g]) x).getD i false else false) =
        l.map fun i => if i < x.length + k then (run gs x).getD i false else false := by
      intro k hk l
      refine List.map_congr_left fun i _ => ?_
      split_ifs with h
      · exact run_prefix gs [g] x i (by omega)
      · rfl
    rcases Nat.lt_or_ge j gs.length with h | h
    · rw [List.getElem_append_left h, same j (by omega), run_prefix gs [g] x _ (by omega)]
      exact ih j h
    · have hjj : j = gs.length := by simp at hj; omega
      subst hjj
      have hg : (gs ++ [g])[gs.length] = g := by simp
      rw [hg, same _ le_rfl, run_snoc, ← hlen, getD_at']
      congr 1
      refine List.map_congr_left fun i _ => ?_
      split_ifs with h
      · rfl
      · exact List.getD_eq_default _ _ (by omega)



theorem mono (gs : List Gate) (x y : List Bool) (hl : x.length = y.length)
    (h : ∀ i, x.getD i false = true → y.getD i false = true)
    (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ i, (run gs x).getD i false = true → (run gs y).getD i false = true := by
  induction gs using List.reverseRecOn with
  | nil => intro i hi; exact h i hi
  | append_singleton gs g ih =>
    intro i hi
    have ih' := ih (fun g hg' => hg g (by simp [hg']))
    have l1 := run_length gs x
    have l2 := run_length gs y
    rw [run_snoc] at hi ⊢
    rcases Nat.lt_trichotomy i (x.length + gs.length) with hlt | heq | hgt
    · rw [getD_lt _ _ _ (by omega)] at hi ⊢; exact ih' i hi
    · have e1 : i = (run gs x).length := by omega
      have e2 : i = (run gs y).length := by omega
      have hi' : g.op.eval (g.inputs.map fun i => (run gs x).getD i false) = true := by
        rw [← getD_at (run gs x) (g.op.eval (g.inputs.map fun i => (run gs x).getD i false)), ← e1]
        exact hi
      rw [e2, getD_at]
      rcases hg g (by simp) with ho | ho
      · rw [ho] at hi' ⊢
        simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id] at hi' ⊢
        exact fun q hq => ih' q (hi' q hq)
      · rw [ho] at hi' ⊢
        simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id] at hi' ⊢
        obtain ⟨q, h1, h2⟩ := hi'
        exact ⟨q, h1, ih' q h2⟩
    · rw [List.getD_eq_default _ _ (by simp; omega)] at hi; cases hi


def tq (Q i : ℕ) : Bool := if i < 13 then Q.testBit i else !(Q.testBit (i - 13) || Q.testBit ((i - 13 + 1) % 13) || Q.testBit ((i - 13 + 3) % 13) || Q.testBit ((i - 13 + 9) % 13))

def LS : List ℕ := [2083, 1100, 4752, 2496, 170, 1328, 1794, 4673, 2069, 7176, 420, 616, 2074, 5252, 4392, 337, 135, 1541, 2626, 1232, 5123, 4233, 564, 270, 3712, 6464, 4196, 2689]

def ptS (Q : ℕ) : Finset (Fin 13) := Finset.univ.filter fun a => Q.testBit (a : ℕ) = true

def FM (Q : ℕ) : Finset (Fin 13) := Finset.univ.filter fun a => tq Q (13 + (a : ℕ)) = true

def adj (i j : ℕ) : Bool := decide (i < 13) && decide (13 ≤ j) && decide ((i + 13 - (j - 13)) % 13 ∈ [0, 1, 3, 9])

theorem cov : ∀ i j : Fin 26, adj i j = false → adj j i = false → ∃ Q ∈ LS, (tq Q i && tq Q j) = true := by decide +kernel

theorem aux : True := trivial

end PEqualNP.Outside.L_meta_7796

theorem PEqualNP.Outside.L_meta_7796 : let x1 : Type := Fin (13 : ℕ); let x2 : Type := Finset x1; have x3 : x1 → x1 → Prop := fun (x3 x4 : x1) => x3 = x4 ∨ x3 = x4 + (1 : x1) ∨ x3 = x4 + (3 : x1) ∨ x3 = x4 + (9 : x1); have x4 : PEqualNP.CircuitLowerBounds.Circuit → x2 → x2 → Bool := fun (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 x6 : x2) => PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x4 fun (x7 : Fin (26 : ℕ)) => Fin.addCases (fun (x8 : Fin (13 : ℕ)) => Decidable.decide (x8 ∈ x5)) (fun (x8 : Fin (13 : ℕ)) => Decidable.decide (x8 ∈ x6)) x7; have x5 : x2 → x2 → Prop := fun (x5 x6 : x2) => (∀ (x7 : x1), x7 ∈ x6 ↔ ∀ x8 ∈ x5, ¬x3 x8 x7) ∧ (∀ x7 ∉ x5, ∃ x9 ∈ x6, x3 x7 x9) ∧ (¬∃ (x7 : x1), ∀ x8 ∈ x5, x3 x8 x7) ∧ ¬∃ (x7 : x1), ∀ x8 ∈ x6, x3 x7 x8; ∀ (x6 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x6 → (∀ (x8 x9 : x2), x5 x8 x9 → x4 x6 x8 x9 = Bool.false) → ∀ (x9 x10 : Fin (26 : ℕ)), (¬∃ (x11 : x1) (x12 : x1), x3 x11 x12 ∧ (x9 = Fin.castAdd (13 : ℕ) x11 ∧ x10 = Fin.natAdd (13 : ℕ) x12 ∨ x10 = Fin.castAdd (13 : ℕ) x11 ∧ x9 = Fin.natAdd (13 : ℕ) x12)) → (PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x6 fun (x12 : Fin (26 : ℕ)) => Decidable.decide (x12 = x9 ∨ x12 = x10)) = Bool.false := by
  intro V SV I ev good C hC hgood a b hab
  have hT : ∀ Q ∈ PEqualNP.Outside.L_meta_7796.LS, good (PEqualNP.Outside.L_meta_7796.ptS Q) (PEqualNP.Outside.L_meta_7796.FM Q) := by
    simp only [good, I]
    decide +kernel
  have hl : ∀ Q ∈ PEqualNP.Outside.L_meta_7796.LS, ∀ i : Fin 26, (Fin.addCases (m := 13) (n := 13) (motive := fun _ => Bool) (fun (x4 : Fin 13) => decide (x4 ∈ PEqualNP.Outside.L_meta_7796.ptS Q)) (fun (x4 : Fin 13) => decide (x4 ∈ PEqualNP.Outside.L_meta_7796.FM Q)) i) = PEqualNP.Outside.L_meta_7796.tq Q i := by decide +kernel
  have hadj : ∀ i j : Fin 26, PEqualNP.Outside.L_meta_7796.adj i j = true → ∃ (x5 : Fin 13) (x6 : Fin 13), (x5 = x6 ∨ x5 = x6 + 1 ∨ x5 = x6 + 3 ∨ x5 = x6 + 9) ∧ (i = Fin.castAdd 13 x5 ∧ j = Fin.natAdd 13 x6) := by
    have h : ∀ i j : Fin 26, PEqualNP.Outside.L_meta_7796.adj i j = true → ((⟨(i : ℕ) % 13, Nat.mod_lt _ (by norm_num)⟩ : Fin 13) = (⟨(j : ℕ) % 13, Nat.mod_lt _ (by norm_num)⟩ : Fin 13) ∨ (⟨(i : ℕ) % 13, Nat.mod_lt _ (by norm_num)⟩ : Fin 13) = (⟨(j : ℕ) % 13, Nat.mod_lt _ (by norm_num)⟩ : Fin 13) + 1 ∨ (⟨(i : ℕ) % 13, Nat.mod_lt _ (by norm_num)⟩ : Fin 13) = (⟨(j : ℕ) % 13, Nat.mod_lt _ (by norm_num)⟩ : Fin 13) + 3 ∨ (⟨(i : ℕ) % 13, Nat.mod_lt _ (by norm_num)⟩ : Fin 13) = (⟨(j : ℕ) % 13, Nat.mod_lt _ (by norm_num)⟩ : Fin 13) + 9) ∧ (i = Fin.castAdd 13 (⟨(i : ℕ) % 13, Nat.mod_lt _ (by norm_num)⟩ : Fin 13) ∧ j = Fin.natAdd 13 (⟨(j : ℕ) % 13, Nat.mod_lt _ (by norm_num)⟩ : Fin 13)) := by decide +kernel
    exact fun i j hij => ⟨_, _, h i j hij⟩
  have h1 : PEqualNP.Outside.L_meta_7796.adj a b = false := by
    by_contra h
    obtain ⟨p, l, h2, h3⟩ := hadj a b (by simpa using h)
    exact hab ⟨p, l, h2, Or.inl h3⟩
  have h2 : PEqualNP.Outside.L_meta_7796.adj b a = false := by
    by_contra h
    obtain ⟨p, l, h2, h3⟩ := hadj b a (by simpa using h)
    exact hab ⟨p, l, h2, Or.inr h3⟩
  obtain ⟨Q, hQ, h⟩ := PEqualNP.Outside.L_meta_7796.cov a b h1 h2
  rw [Bool.and_eq_true] at h
  have hz := hgood _ _ (hT Q hQ)
  cases hv : PEqualNP.MetaComplexity.circuitFun 26 C fun (x12 : Fin 26) => decide (x12 = a ∨ x12 = b) with
  | false => rfl
  | true =>
    have := PEqualNP.Outside.L_meta_7796.mono C.gates (List.ofFn fun (x12 : Fin 26) => decide (x12 = a ∨ x12 = b)) (List.ofFn fun (i : Fin 26) => PEqualNP.Outside.L_meta_7796.tq Q i) (by simp) (fun i hi => ?_) (fun g hg => by simpa using (hC g hg).1) C.output hv
    · have e : (fun (i : Fin 26) => PEqualNP.Outside.L_meta_7796.tq Q i) = fun (i : Fin 26) => (Fin.addCases (m := 13) (n := 13) (motive := fun _ => Bool) (fun (x4 : Fin 13) => decide (x4 ∈ PEqualNP.Outside.L_meta_7796.ptS Q)) (fun (x4 : Fin 13) => decide (x4 ∈ PEqualNP.Outside.L_meta_7796.FM Q)) i) := by
        funext i; exact (hl Q hQ i).symm
      rw [e] at this
      exact absurd (this.symm.trans hz) (by simp)
    · by_cases hin : i < 26
      · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hin, dite_true, Option.getD_some, decide_eq_true_eq] at hi ⊢
        rcases hi with hi | hi
        · rw [← hi] at h; exact h.1
        · rw [← hi] at h; exact h.2
      · rw [List.getD_eq_default _ _ (by simp; omega)] at hi; cases hi
