import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1655

open PEqualNP.CircuitLowerBounds

-- One gate of a straight-line program: append the value of the gate on the wires so far.
def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (gs : List Gate) (o : ℕ) (y : List Bool) :
    Circuit.wires ⟨gs, o⟩ y = gs.foldl step y := rfl

theorem eval_eq (gs : List Gate) (o : ℕ) (y : List Bool) :
    Circuit.eval ⟨gs, o⟩ y = (gs.foldl step y).getD o false := rfl

theorem foldl_prefix (gs : List Gate) (w : List Bool) : ∃ s, gs.foldl step w = w ++ s := by
  induction gs generalizing w with
  | nil => exact ⟨[], by simp⟩
  | cons g gs ih =>
    obtain ⟨s, hs⟩ := ih (step w g)
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: s, ?_⟩
    rw [List.foldl_cons, hs]
    simp [step]

theorem foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [step]
    omega

theorem getD_prefix (w s : List Bool) (i : ℕ) (h : i < w.length) :
    (w ++ s).getD i false = w.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem fold_gate (gs : List Gate) (w : List Bool) (k : ℕ) (hk : k < gs.length)
    (hin : ∀ i ∈ (gs[k]).inputs, i < w.length + k) :
    (gs.foldl step w).getD (w.length + k) false =
      (gs[k]).op.eval ((gs[k]).inputs.map fun i => (gs.foldl step w).getD i false) := by
  induction gs generalizing w k with
  | nil => simp at hk
  | cons g gs ih =>
    cases k with
    | zero =>
      obtain ⟨s, hs⟩ := foldl_prefix gs (step w g)
      simp only [List.foldl_cons, List.getElem_cons_zero, Nat.add_zero] at hin ⊢
      rw [hs]
      have hl : w.length < (step w g).length := by simp [step]
      rw [getD_prefix _ _ _ hl]
      have h1 : (step w g).getD w.length false =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp [step, List.getD_eq_getElem?_getD]
      rw [h1]
      congr 1
      apply List.map_congr_left
      intro i hi
      have hi' := hin i hi
      rw [getD_prefix _ _ _ (by omega), step, getD_prefix _ _ _ hi']
    | succ k =>
      simp only [List.foldl_cons, List.getElem_cons_succ] at hin ⊢
      have hl : (step w g).length = w.length + 1 := by simp [step]
      have := ih (step w g) k (by simp at hk; omega) (by
        intro i hi
        rw [hl]
        have := hin i hi
        omega)
      rw [hl] at this
      rw [show w.length + (k + 1) = w.length + 1 + k by omega]
      exact this

theorem eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (l : List ℕ)
    (a b : ℕ → Bool) (h : ∀ i ∈ l, a i = true → b i = true)
    (ha : op.eval (l.map a) = true) : op.eval (l.map b) = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id] at ha ⊢
    intro i hi
    exact h i hi (ha i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id] at ha ⊢
    obtain ⟨i, hi, h'⟩ := ha
    exact ⟨i, hi, h i hi h'⟩

end PEqualNP.Outside.L_meta_1655

open PEqualNP.Outside.L_meta_1655 PEqualNP.CircuitLowerBounds

theorem PEqualNP.Outside.L_meta_1655 : ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (i0 p0 p1 : Fin N),
    2 ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    p0 ≠ p1 → p0 ∈ L i0 → p1 ∈ L i0 →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : Fin N → ℕ) (j h : Fin gates.length),
    (∀ gt ∈ gates, (gt.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ gt.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ gt.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ gt.inputs.length ≤ 2) →
    (∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < N + (i : ℕ)) →
    (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → (∀ i : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) →
    h < j → (∃ r : List ℕ, (gates.get j).inputs = (N + (h : ℕ)) :: r) →
    (∀ (t : Fin N) (x : Fin N → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o t⟩ (List.ofFn x) = decide (∃ v ∈ L t, x v = true)) →
    ∀ ev : ℕ → (Fin N → Bool) → Bool, (∀ (w : ℕ) (x : Fin N → Bool), ev w x = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w⟩ (List.ofFn x)) →
    ev (N + (h : ℕ)) (fun v : Fin N => decide (v = p0)) = true → ev (N + (h : ℕ)) (fun v : Fin N => decide (v = p1)) = true → (∀ p : Fin N, p ≠ p0 → p ≠ p1 → ev (N + (h : ℕ)) (fun v : Fin N => decide (v = p)) = false) →
    ev (N + (h : ℕ)) (fun v : Fin N => decide (v ∉ L i0)) = false →
    ∀ Sm Dm : Fin N → ℕ → Prop,
    (∀ (t : Fin N) (w : ℕ), Sm t w ↔ ∀ x : Fin N → Bool, (∀ v : Fin N, x v = true → v ∉ L i0) → ev w x = true → ∃ v ∈ L t, x v = true) →
    (∀ (t : Fin N) (w : ℕ), Dm t w ↔ (Sm t w ∧ ∀ p ∈ L i0, ev w (fun v : Fin N => decide (v = p)) = true → p ∈ L t)) →
    ∀ Vs : Fin N → ℕ → Fin N → Prop,
    (∀ (t : Fin N) (w : ℕ) (v : Fin N), Vs t w v ↔ ((Dm t w ∧ ev w (fun uu : Fin N => decide (uu = v)) = true) ∨ (¬ Dm t w ∧ v ∉ L i0 ∧ ev w (fun uu : Fin N => decide (uu = v)) = true))) →
    ∀ t : Fin N,
    (∀ (w : ℕ) (v : Fin N), Dm t w → ev w (fun uu : Fin N => decide (uu = v)) = true → v ∈ L t) ∧
    (∀ (w : ℕ) (v : Fin N), Sm t w → v ∉ L i0 → ev w (fun uu : Fin N => decide (uu = v)) = true → v ∈ L t) ∧
    (∀ g : Fin gates.length, (gates.get g).op = PEqualNP.CircuitLowerBounds.GateOp.or → (Sm t (N + (g : ℕ)) → ∀ e ∈ (gates.get g).inputs, Sm t e) ∧ (Dm t (N + (g : ℕ)) → ∀ e ∈ (gates.get g).inputs, Dm t e)) ∧
    (∀ g : Fin gates.length, (gates.get g).op = PEqualNP.CircuitLowerBounds.GateOp.and → Sm t (N + (g : ℕ)) → ∃ e ∈ (gates.get g).inputs, Sm t e) ∧
    (∀ (w : ℕ) (v : Fin N), Sm t w → Vs t w v → v ∈ L t) := by
  intro q N L i0 p0 p1 _ _ _ _ _ _ _ _ gates o j h hops hinb hjnot hjuniq hhj hjin _ ev hev _ _ _
    hcomp Sm Dm hSm hDm Vs hVs t
  -- W x w is the value of wire w on input x.
  let W : (Fin N → Bool) → ℕ → Bool := fun x w => (gates.foldl step (List.ofFn x)).getD w false
  have hevW : ∀ w x, ev w x = W x w := fun w x => (hev w x).trans (eval_eq gates w _)
  have gateW : ∀ (g : Fin gates.length) (x : Fin N → Bool),
      W x (N + g) = (gates.get g).op.eval ((gates.get g).inputs.map (W x)) := by
    intro g x
    have := fold_gate gates (List.ofFn x) g g.isLt (by
      intro i hi
      rw [List.length_ofFn]
      exact hinb g i (by simpa using hi))
    rw [List.length_ofFn] at this
    show (gates.foldl step (List.ofFn x)).getD (N + g) false = (gates.get g).op.eval
      ((gates.get g).inputs.map fun i => (gates.foldl step (List.ofFn x)).getD i false)
    rw [List.get_eq_getElem]
    exact this
  have inW : ∀ (x : Fin N → Bool) (v : Fin N), W x v = x v := by
    intro x v
    obtain ⟨s, hs⟩ := foldl_prefix gates (List.ofFn x)
    show (gates.foldl step (List.ofFn x)).getD v false = x v
    rw [hs, getD_prefix _ _ _ (by simp)]
    simp [List.getD_eq_getElem?_getD]
  have outW : ∀ (x : Fin N → Bool) (w : ℕ), N + gates.length ≤ w → W x w = false := by
    intro x w hw
    show (gates.foldl step (List.ofFn x)).getD w false = false
    apply List.getD_eq_default
    rw [foldl_length, List.length_ofFn]
    exact hw
  have opnot : ∀ g : Fin gates.length, (gates.get g).op ≠ GateOp.not →
      (gates.get g).op = GateOp.and ∨ (gates.get g).op = GateOp.or := by
    intro g hg
    rcases (hops _ (List.get_mem gates g)).1 with h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr h1
    · exact absurd h1 hg
  -- Below the NOT gate every wire is monotone.
  have monoA : ∀ w : ℕ, w < N + j → ∀ x y : Fin N → Bool, (∀ v, x v = true → y v = true) →
      W x w = true → W y w = true := by
    intro w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro hw x y hxy hx
      by_cases hwN : w < N
      · have e1 := inW x ⟨w, hwN⟩
        have e2 := inW y ⟨w, hwN⟩
        simp only at e1 e2
        rw [e1] at hx
        rw [e2]
        exact hxy _ hx
      · have hgl : w - N < gates.length := by omega
        let g : Fin gates.length := ⟨w - N, hgl⟩
        have hwg : w = N + (g : ℕ) := by simp [g]; omega
        have hgj : g ≠ j := by
          intro e
          have : (g : ℕ) = (j : ℕ) := by rw [e]
          simp [g] at this
          omega
        have hop := opnot g (fun hn => hgj (hjuniq g hn))
        rw [hwg, gateW] at hx ⊢
        apply eval_mono _ hop _ _ _ _ hx
        intro i hi
        have hi1 := hinb g i hi
        exact ih i (by omega) (by omega) x y hxy
  -- On inputs that avoid the line i0 the NOT gate is true, so every wire is monotone there.
  have monoB : ∀ w : ℕ, ∀ x y : Fin N → Bool, (∀ v, x v = true → y v = true) →
      (∀ v, y v = true → v ∉ L i0) → W x w = true → W y w = true := by
    intro w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro x y hxy hy hx
      by_cases hwN : w < N
      · exact monoA w (by omega) x y hxy hx
      · by_cases hwl : N + gates.length ≤ w
        · rw [outW x w hwl] at hx
          exact absurd hx (by simp)
        · have hgl : w - N < gates.length := by omega
          let g : Fin gates.length := ⟨w - N, hgl⟩
          have hwg : w = N + (g : ℕ) := by simp [g]; omega
          by_cases hn : (gates.get g).op = GateOp.not
          · have hgj := hjuniq g hn
            obtain ⟨r, hr⟩ := hjin
            have hyh : W y (N + h) = false := by
              by_contra hc
              have hc' : W y (N + h) = true := by simpa using hc
              have := monoA (N + h) (by have hv : (h : ℕ) < j := hhj; omega) y
                (fun v => decide (v ∉ L i0)) (fun v hv => by simpa using hy v hv) hc'
              rw [← hevW] at this
              rw [hcomp] at this
              exact absurd this (by simp)
            rw [hwg, gateW, hgj, hjnot, hr]
            simp [GateOp.eval, hyh]
          · have hop := opnot g hn
            rw [hwg, gateW] at hx ⊢
            apply eval_mono _ hop _ _ _ _ hx
            intro i hi
            have hi1 := hinb g i hi
            exact ih i (by omega) x y hxy hy
  have pt : ∀ (w : ℕ) (v : Fin N), Sm t w → v ∉ L i0 →
      ev w (fun uu : Fin N => decide (uu = v)) = true → v ∈ L t := by
    intro w v hS hv he
    obtain ⟨u, hu, hu'⟩ := (hSm t w).1 hS _ (fun u hu => by
      simp at hu
      rw [hu]
      exact hv) he
    simp at hu'
    rw [hu'] at hu
    exact hu
  have c1 : ∀ (w : ℕ) (v : Fin N), Dm t w →
      ev w (fun uu : Fin N => decide (uu = v)) = true → v ∈ L t := by
    intro w v hD he
    have hD' := (hDm t w).1 hD
    by_cases hv : v ∈ L i0
    · exact hD'.2 v hv he
    · exact pt w v hD'.1 hv he
  have orUp : ∀ g : Fin gates.length, (gates.get g).op = GateOp.or →
      ∀ e ∈ (gates.get g).inputs, ∀ x, ev e x = true → ev (N + g) x = true := by
    intro g hop e he x hx
    rw [hevW] at hx ⊢
    rw [gateW, hop]
    simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id]
    exact ⟨e, he, hx⟩
  refine ⟨c1, pt, ?_, ?_, ?_⟩
  · intro g hop
    have hS : Sm t (N + g) → ∀ e ∈ (gates.get g).inputs, Sm t e := by
      intro hS e he
      rw [hSm] at hS ⊢
      intro x hx hex
      exact hS x hx (orUp g hop e he x hex)
    refine ⟨hS, ?_⟩
    intro hD e he
    have hD' := (hDm t _).1 hD
    rw [hDm]
    exact ⟨hS hD'.1 e he, fun p hp hpe => hD'.2 p hp (orUp g hop e he _ hpe)⟩
  · intro g hop hS
    by_contra hno
    push_neg at hno
    have hno' : ∀ e ∈ (gates.get g).inputs, ∃ x : Fin N → Bool,
        (∀ v, x v = true → v ∉ L i0) ∧ W x e = true ∧ ∀ v ∈ L t, x v = false := by
      intro e he
      have := hno e he
      rw [hSm] at this
      push_neg at this
      obtain ⟨x, hx, hex, hm⟩ := this
      exact ⟨x, hx, by rw [← hevW]; exact hex, fun v hv => by simpa using hm v hv⟩
    have hlen := (hops _ (List.get_mem gates g)).2
    have hS' := (hSm t _).1 hS
    rcases hI : (gates.get g).inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, r⟩⟩⟩
    · obtain ⟨v, hv, hv'⟩ := hS' (fun _ => false) (by simp) (by
        rw [hevW, gateW, hop, hI]
        simp [GateOp.eval])
      exact absurd hv' (by simp)
    · obtain ⟨xa, hxa, hwa, hma⟩ := hno' a (by rw [hI]; simp)
      obtain ⟨v, hv, hv'⟩ := hS' xa hxa (by
        rw [hevW, gateW, hop, hI]
        simpa [GateOp.eval] using hwa)
      rw [hma v hv] at hv'
      exact absurd hv' (by simp)
    · obtain ⟨xa, hxa, hwa, hma⟩ := hno' a (by rw [hI]; simp)
      obtain ⟨xb, hxb, hwb, hmb⟩ := hno' b (by rw [hI]; simp)
      let y : Fin N → Bool := fun v => xa v || xb v
      have hy : ∀ v, y v = true → v ∉ L i0 := by
        intro v hv
        simp only [y, Bool.or_eq_true] at hv
        rcases hv with hv | hv
        · exact hxa v hv
        · exact hxb v hv
      have hya := monoB a xa y (fun v hv => by simp [y, hv]) hy hwa
      have hyb := monoB b xb y (fun v hv => by simp [y, hv]) hy hwb
      obtain ⟨v, hv, hv'⟩ := hS' y hy (by
        rw [hevW, gateW, hop, hI]
        simp [GateOp.eval, hya, hyb])
      simp [y, hma v hv, hmb v hv] at hv'
    · rw [hI] at hlen
      simp at hlen
  · intro w v hS hV
    rcases (hVs t w v).1 hV with ⟨hD, he⟩ | ⟨_, hv, he⟩
    · exact c1 w v hD he
    · exact pt w v hS hv he
