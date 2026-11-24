import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4708
open PEqualNP.CircuitLowerBounds

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wf_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    wf (gs ++ [g]) w = wf gs w ++ [g.op.eval (g.inputs.map fun i => (wf gs w).getD i false)] := by
  simp [wf, List.foldl_append]

theorem wf_len (gs : List Gate) : ∀ w : List Bool, (wf gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [wf]
  | cons g gs ih =>
    intro w
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]; simp; omega

theorem wf_keep (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (wf gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) i (by simp; omega)
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem wf_prefix (pre post : List Gate) (w : List Bool) (i : ℕ)
    (hi : i < w.length + pre.length) :
    (wf (pre ++ post) w).getD i false = (wf pre w).getD i false := by
  have : wf (pre ++ post) w = wf post (wf pre w) := by simp [wf, List.foldl_append]
  rw [this]
  exact wf_keep post _ i (by rw [wf_len]; exact hi)

theorem getD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
  simp [List.getD_eq_getElem?_getD]

theorem wire_take (gates : List Gate) (X : List Bool) (k i : ℕ) (hi : i < X.length + k)
    (hk : k ≤ gates.length) :
    (wf gates X).getD i false = (wf (gates.take k) X).getD i false := by
  conv_lhs => rw [← List.take_append_drop k gates]
  exact wf_prefix _ _ _ _ (by rw [List.length_take, Nat.min_eq_left hk]; exact hi)

theorem gate_val (gates : List Gate) (X : List Bool) (k : ℕ) (hk : k < gates.length) :
    (wf gates X).getD (X.length + k) false
      = gates[k].op.eval (gates[k].inputs.map fun i => (wf (gates.take k) X).getD i false) := by
  rw [wire_take gates X (k + 1) _ (by omega) hk, List.take_succ_eq_append_getElem hk, wf_snoc]
  have := getD_snoc_eq (wf (gates.take k) X)
    (gates[k].op.eval (gates[k].inputs.map fun i => (wf (gates.take k) X).getD i false))
  rw [wf_len, List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)] at this
  exact this

theorem gate_full (gates : List Gate) (X : List Bool) (k : ℕ) (hk : k < gates.length)
    (hrb : ∀ i ∈ gates[k].inputs, i < X.length + k) :
    (wf gates X).getD (X.length + k) false
      = gates[k].op.eval (gates[k].inputs.map fun i => (wf gates X).getD i false) := by
  rw [gate_val gates X k hk]
  congr 1
  apply List.map_congr_left
  intro i hi
  exact (wire_take gates X k i (hrb i hi) (le_of_lt hk)).symm

theorem getD_ofFn {n : ℕ} (f : Fin n → Bool) (i : Fin n) :
    (List.ofFn f).getD (i : ℕ) false = f i := by
  simp

theorem gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) :
    PEqualNP.MetaComplexity.NestedCover.gateAt C k = C.gates[k] := by
  unfold PEqualNP.MetaComplexity.NestedCover.gateAt
  rw [List.getD_eq_getElem _ _ hk]

end PEqualNP.Outside.L_meta_4708

open PEqualNP.Outside.L_meta_4708 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_4708 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 → PEqualNP.MetaComplexity.NestedCover.ReadsBack x1 x2 → x2.output < x1 + x2.size → (∀ (x6 : Fin x1), (PEqualNP.MetaComplexity.circuitFun x1 x2 fun (x7 : Fin x1) => Decidable.decide (x7 = x6)) = Bool.false) → ∃ (x7 : Finset ℕ), (∀ x8 ∈ x7, x8 < x2.size ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x8).op = PEqualNP.CircuitLowerBounds.GateOp.and) ∧ ∀ (x8 : Fin x1 → Bool), PEqualNP.MetaComplexity.circuitFun x1 x2 x8 = Bool.true ↔ ∃ x9 ∈ x7, PEqualNP.EdgeOwnership.gateVal x1 x2 x9 x8 = Bool.true := by
  intro n C hC hrb hout h1
  classical
  have hrb' : ∀ j (hj : j < C.gates.length), ∀ i ∈ C.gates[j].inputs, i < n + j :=
    fun j hj i hi => hrb j hj i (by rw [gateAt_eq C j hj]; exact hi)
  have gv : ∀ (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length),
      PEqualNP.EdgeOwnership.gateVal n C k x = (C.gates[k]).op.eval
        (C.gates[k].inputs.map fun i => (wf C.gates (List.ofFn x)).getD i false) := by
    intro x k hk
    have h2 := gate_full C.gates (List.ofFn x) k hk (by
      intro i hi
      rw [List.length_ofFn]
      exact hrb' k hk i hi)
    rw [List.length_ofFn] at h2
    exact h2
  have hwv : ∀ (x : Fin n → Bool) (w : ℕ), n ≤ w →
      (wf C.gates (List.ofFn x)).getD w false = PEqualNP.EdgeOwnership.gateVal n C (w - n) x := by
    intro x w hw
    show _ = (wf C.gates (List.ofFn x)).getD (n + (w - n)) false
    congr 1
    omega
  have hin : ∀ (x : Fin n → Bool) (i : ℕ) (hi : i < n),
      (wf C.gates (List.ofFn x)).getD i false = x ⟨i, hi⟩ := by
    intro x i hi
    rw [wf_keep _ _ i (by rw [List.length_ofFn]; exact hi)]
    exact getD_ofFn x ⟨i, hi⟩
  have hf : ∀ x : Fin n → Bool, PEqualNP.MetaComplexity.circuitFun n C x
      = (wf C.gates (List.ofFn x)).getD C.output false := fun _ => rfl
  have hno : ∀ (i : ℕ) (hi : i < n), ¬ (∀ y : Fin n → Bool,
      (wf C.gates (List.ofFn y)).getD i false = true →
      PEqualNP.MetaComplexity.circuitFun n C y = true) := by
    intro i hi hall
    have h2 := hall (fun z => decide (z = ⟨i, hi⟩)) (by rw [hin _ i hi]; exact decide_eq_true rfl)
    rw [h1 ⟨i, hi⟩] at h2
    exact absurd h2 (by decide)
  refine ⟨(Finset.range C.gates.length).filter (fun g =>
    (PEqualNP.MetaComplexity.NestedCover.gateAt C g).op = GateOp.and ∧
    ∀ y : Fin n → Bool, PEqualNP.EdgeOwnership.gateVal n C g y = true →
      PEqualNP.MetaComplexity.circuitFun n C y = true), ?_, ?_⟩
  · intro g hg
    obtain ⟨h2, h3, _⟩ := Finset.mem_filter.1 hg
    exact ⟨Finset.mem_range.1 h2, h3⟩
  · intro x
    constructor
    · intro hx
      have K : ∀ k, k < C.gates.length →
          (∀ y : Fin n → Bool, PEqualNP.EdgeOwnership.gateVal n C k y = true →
            PEqualNP.MetaComplexity.circuitFun n C y = true) →
          PEqualNP.EdgeOwnership.gateVal n C k x = true →
          ∃ g ∈ (Finset.range C.gates.length).filter (fun g =>
            (PEqualNP.MetaComplexity.NestedCover.gateAt C g).op = GateOp.and ∧
            ∀ y : Fin n → Bool, PEqualNP.EdgeOwnership.gateVal n C g y = true →
              PEqualNP.MetaComplexity.circuitFun n C y = true),
            PEqualNP.EdgeOwnership.gateVal n C g x = true := by
        intro k
        induction k using Nat.strong_induction_on with
        | _ k ih =>
          intro hk hbel hval
          rcases (hC _ (List.getElem_mem hk)).1 with hop | hop
          · exact ⟨k, Finset.mem_filter.2 ⟨Finset.mem_range.2 hk,
              by rw [gateAt_eq C k hk]; exact hop, hbel⟩, hval⟩
          · have hop' : (C.gates[k]).op = GateOp.or := hop
            have hv2 := hval
            rw [gv x k hk, hop'] at hv2
            simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id] at hv2
            obtain ⟨i, hi, hiv⟩ := hv2
            have hib : ∀ y : Fin n → Bool, (wf C.gates (List.ofFn y)).getD i false = true →
                PEqualNP.MetaComplexity.circuitFun n C y = true := by
              intro y hy
              apply hbel y
              rw [gv y k hk, hop']
              simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
              exact ⟨i, hi, hy⟩
            by_cases hin2 : i < n
            · exact absurd hib (hno i hin2)
            · have hik := hrb' k hk i hi
              apply ih (i - n) (by omega) (by omega)
              · intro y hy
                apply hib y
                rw [hwv y i (by omega)]
                exact hy
              · rw [← hwv x i (by omega)]
                exact hiv
      by_cases ho : C.output < n
      · exact absurd (fun y hy => hy) (hno C.output ho)
      · have hk0 : C.output - n < C.gates.length := by
          have : C.output < n + C.gates.length := hout
          omega
        apply K (C.output - n) hk0
        · intro y hy
          rw [hf, hwv y C.output (by omega)]
          exact hy
        · rw [← hwv x C.output (by omega)]
          exact hx
    · rintro ⟨g, hg, hgv⟩
      exact (Finset.mem_filter.1 hg).2.2 x hgv
