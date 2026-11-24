import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_4356

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

lemma run_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    run (gs ++ [g]) x = run gs x ++ [g.op.eval (g.inputs.map fun i => (run gs x).getD i false)] := by
  simp [run, List.foldl_append]

lemma run_length (gs : List Gate) (x : List Bool) :
    (run gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton gs g ih => rw [run_snoc]; simp [ih]; omega

lemma run_getD (gs : List Gate) (x : List Bool) (w : ℕ) (hw : w < x.length) :
    (run gs x).getD w false = x.getD w false := by
  induction gs using List.reverseRecOn with
  | nil => rfl
  | append_singleton gs g ih =>
    rw [run_snoc, List.getD_append _ _ _ _ (by rw [run_length]; omega), ih]

lemma snoc_getD (gs : List Gate) (g : Gate) (x : List Bool) (w : ℕ) (hw : w < x.length + gs.length) :
    (run (gs ++ [g]) x).getD w false = (run gs x).getD w false := by
  rw [run_snoc, List.getD_append _ _ _ _ (by rw [run_length]; omega)]

lemma snoc_last (gs : List Gate) (g : Gate) (x : List Bool) :
    (run (gs ++ [g]) x).getD (x.length + gs.length) false =
      g.op.eval (g.inputs.map fun i => (run gs x).getD i false) := by
  rw [run_snoc, List.getD_append_right _ _ _ _ (by rw [run_length])]
  simp [run_length]

lemma snoc_out (gs : List Gate) (g : Gate) (x : List Bool) (w : ℕ) (hw : x.length + gs.length < w) :
    (run (gs ++ [g]) x).getD w false = false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [run_length]; simp; omega)]
  rfl

def row (x : Fin 6 → Bool) : List Bool := [x 0, x 1, false, x 2, x 3, x 4, x 5]

def Realized (f : (Fin 6 → Bool) → Bool) (D : List Gate) : Prop :=
  (∃ b : Bool, f = fun _ => b) ∨
    ∃ k, k < 6 + D.length ∧ f = fun x => (run D (List.ofFn x)).getD k false

def Ok (D : List Gate) : Prop :=
  ∀ g ∈ D, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

def wf (gs : List Gate) (i : ℕ) : (Fin 6 → Bool) → Bool := fun x => (run gs (row x)).getD i false

def T (gs : List Gate) : Finset ((Fin 6 → Bool) → Bool) :=
  ((Finset.range (7 + gs.length)).image (wf gs)).filter
    (fun f => ∀ r : Fin 8, ∃ x, f x ≠ (false :: true :: List.ofFn x).getD r.val false)

lemma realized_mono (f : (Fin 6 → Bool) → Bool) (D : List Gate) (g : Gate) (h : Realized f D) :
    Realized f (D ++ [g]) := by
  rcases h with h | ⟨k, hk, hf⟩
  · exact Or.inl h
  · refine Or.inr ⟨k, by simp; omega, ?_⟩
    rw [hf]
    funext x
    rw [snoc_getD _ _ _ _ (by simp; omega)]

lemma wire_var (D : List Gate) (m : ℕ) (hm : m < 6) (x : Fin 6 → Bool) :
    (run D (List.ofFn x)).getD m false = x ⟨m, hm⟩ := by
  rw [run_getD _ _ _ (by simp; omega)]
  simp [List.getD_eq_getElem?_getD, hm]
  interval_cases m <;> rfl

lemma nontriv_of (f : (Fin 6 → Bool) → Bool) (D : List Gate) (h : ¬ Realized f D) :
    ∀ r : Fin 8, ∃ x, f x ≠ (false :: true :: List.ofFn x).getD r.val false := by
  intro r
  by_contra hc
  push Not at hc
  apply h
  have hf : f = fun x => (false :: true :: List.ofFn x).getD r.val false := funext hc
  rcases r with ⟨r, hr⟩
  rcases r with _ | _ | m
  · exact Or.inl ⟨false, hf⟩
  · exact Or.inl ⟨true, hf⟩
  · refine Or.inr ⟨m, by omega, ?_⟩
    rw [hf]
    funext x
    rw [wire_var D m (by omega)]
    obtain ⟨hm6⟩ : PLift (m < 6) := ⟨by omega⟩
    interval_cases m <;> rfl


lemma gate (D : List Gate) (g : Gate)
    (hg : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (F : ℕ → (Fin 6 → Bool) → Bool) (hF : ∀ i, Realized (F i) D) :
    Realized (fun x => g.op.eval (g.inputs.map fun i => F i x)) D ∨
    ∃ g' : Gate, (g'.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
        g'.inputs.length ≤ 2) ∧
      (fun x => g.op.eval (g.inputs.map fun i => F i x)) =
        fun x => g'.op.eval (g'.inputs.map fun k => (run D (List.ofFn x)).getD k false) := by
  obtain ⟨op, l⟩ := g
  obtain ⟨hop, hl⟩ := hg
  simp only at hop hl ⊢
  have hop' : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not := by simpa using hop
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
  · exact Or.inl (Or.inl ⟨op.eval [], rfl⟩)
  · rcases hF a with ⟨u, hu⟩ | ⟨k, hk, hu⟩
    · exact Or.inl (Or.inl ⟨op.eval [u], by funext x; simp [hu]⟩)
    · rcases hop' with rfl | rfl | rfl
      · exact Or.inl (Or.inr ⟨k, hk, by funext x; simp [hu, GateOp.eval]⟩)
      · exact Or.inl (Or.inr ⟨k, hk, by funext x; simp [hu, GateOp.eval]⟩)
      · exact Or.inr ⟨⟨GateOp.not, [k]⟩, by simp, by funext x; simp [hu]⟩
  · rcases hF a with ⟨u, hu⟩ | ⟨k, hk, hu⟩ <;> rcases hF b with ⟨v, hv⟩ | ⟨m, hm, hv⟩
    · exact Or.inl (Or.inl ⟨op.eval [u, v], by funext x; simp [hu, hv]⟩)
    · rcases hop' with rfl | rfl | rfl <;> cases u
      · exact Or.inl (Or.inl ⟨false, by funext x; simp [hu, hv, GateOp.eval]⟩)
      · exact Or.inl (Or.inr ⟨m, hm, by funext x; simp [hu, hv, GateOp.eval]⟩)
      · exact Or.inl (Or.inr ⟨m, hm, by funext x; simp [hu, hv, GateOp.eval]⟩)
      · exact Or.inl (Or.inl ⟨true, by funext x; simp [hu, hv, GateOp.eval]⟩)
      · exact Or.inl (Or.inl ⟨true, by funext x; simp [hu, hv, GateOp.eval]⟩)
      · exact Or.inl (Or.inl ⟨false, by funext x; simp [hu, hv, GateOp.eval]⟩)
    · rcases hop' with rfl | rfl | rfl
      · cases v
        · exact Or.inl (Or.inl ⟨false, by funext x; simp [hu, hv, GateOp.eval]⟩)
        · exact Or.inl (Or.inr ⟨k, hk, by funext x; simp [hu, hv, GateOp.eval]⟩)
      · cases v
        · exact Or.inl (Or.inr ⟨k, hk, by funext x; simp [hu, hv, GateOp.eval]⟩)
        · exact Or.inl (Or.inl ⟨true, by funext x; simp [hu, hv, GateOp.eval]⟩)
      · exact Or.inr ⟨⟨GateOp.not, [k]⟩, by simp, by funext x; simp [hu, GateOp.eval]⟩
    · exact Or.inr ⟨⟨op, [k, m]⟩, ⟨hop, by simp⟩, by funext x; simp [hu, hv]⟩
  · simp at hl

lemma wf_snoc_lt (gs : List Gate) (g : Gate) (i : ℕ) (hi : i < 7 + gs.length) :
    wf (gs ++ [g]) i = wf gs i := by
  funext x
  exact snoc_getD _ _ _ _ (by simp [row]; omega)

lemma wf_snoc_last (gs : List Gate) (g : Gate) :
    wf (gs ++ [g]) (7 + gs.length) = fun x => g.op.eval (g.inputs.map fun i => wf gs i x) := by
  funext x
  exact snoc_last gs g (row x)

lemma wf_snoc_out (gs : List Gate) (g : Gate) (i : ℕ) (hi : 7 + gs.length < i) :
    wf (gs ++ [g]) i = fun _ => false := by
  funext x
  exact snoc_out _ _ _ _ (by simp [row]; omega)

lemma base (i : ℕ) : Realized (wf [] i) [] := by
  by_cases hi : i < 7
  · interval_cases i
    · exact Or.inr ⟨0, by simp, by funext x; rw [wire_var [] 0 (by omega)]; rfl⟩
    · exact Or.inr ⟨1, by simp, by funext x; rw [wire_var [] 1 (by omega)]; rfl⟩
    · exact Or.inl ⟨false, rfl⟩
    · exact Or.inr ⟨2, by simp, by funext x; rw [wire_var [] 2 (by omega)]; rfl⟩
    · exact Or.inr ⟨3, by simp, by funext x; rw [wire_var [] 3 (by omega)]; rfl⟩
    · exact Or.inr ⟨4, by simp, by funext x; rw [wire_var [] 4 (by omega)]; rfl⟩
    · exact Or.inr ⟨5, by simp, by funext x; rw [wire_var [] 5 (by omega)]; rfl⟩
  · refine Or.inl ⟨false, ?_⟩
    funext x
    simp only [wf, run, List.foldl_nil]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp [row]; omega)]
    rfl

lemma main (gs : List Gate) (hok : Ok gs) :
    ∃ D : List Gate, Ok D ∧ D.length ≤ (T gs).card ∧ ∀ i, Realized (wf gs i) D := by
  induction gs using List.reverseRecOn with
  | nil => exact ⟨[], fun g hg => by simp at hg, Nat.zero_le _, base⟩
  | append_singleton gs g ih =>
    obtain ⟨D, hD, hlen, hR⟩ := ih (fun g' hg' => hok g' (by simp [hg']))
    have hg := hok g (by simp)
    have hsub : T gs ⊆ T (gs ++ [g]) := by
      intro f hf
      simp only [T, Finset.mem_filter, Finset.mem_image, Finset.mem_range] at hf ⊢
      obtain ⟨⟨i, hi, rfl⟩, hn⟩ := hf
      exact ⟨⟨i, by simp; omega, wf_snoc_lt gs g i hi⟩, hn⟩
    have hlast := wf_snoc_last gs g
    by_cases hr : Realized (wf (gs ++ [g]) (7 + gs.length)) D
    · refine ⟨D, hD, hlen.trans (Finset.card_le_card hsub), ?_⟩
      intro i
      rcases lt_trichotomy i (7 + gs.length) with h | rfl | h
      · rw [wf_snoc_lt gs g i h]; exact hR i
      · exact hr
      · rw [wf_snoc_out gs g i h]; exact Or.inl ⟨false, rfl⟩
    · have hr' := hr
      rw [hlast] at hr'
      rcases gate D g hg (wf gs) hR with hx | ⟨g', hg', heq⟩
      · exact absurd hx hr'
      refine ⟨D ++ [g'], ?_, ?_, ?_⟩
      · intro x hx
        simp only [List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | rfl
        · exact hD x hx
        · exact hg'
      · have hnot : wf (gs ++ [g]) (7 + gs.length) ∉ T gs := by
          intro hm
          simp only [T, Finset.mem_filter, Finset.mem_image, Finset.mem_range] at hm
          obtain ⟨⟨i, hi, hi'⟩, -⟩ := hm
          exact hr (hi' ▸ hR i)
        have hin : wf (gs ++ [g]) (7 + gs.length) ∈ T (gs ++ [g]) := by
          simp only [T, Finset.mem_filter, Finset.mem_image, Finset.mem_range]
          exact ⟨⟨7 + gs.length, by simp, rfl⟩, nontriv_of _ D hr⟩
        have h1 : insert (wf (gs ++ [g]) (7 + gs.length)) (T gs) ⊆ T (gs ++ [g]) :=
          Finset.insert_subset hin hsub
        have h2 := Finset.card_le_card h1
        rw [Finset.card_insert_of_notMem hnot] at h2
        simp only [List.length_append, List.length_singleton]
        omega
      · intro i
        rcases lt_trichotomy i (7 + gs.length) with h | rfl | h
        · rw [wf_snoc_lt gs g i h]; exact realized_mono _ _ _ (hR i)
        · refine Or.inr ⟨6 + D.length, by simp, ?_⟩
          rw [hlast, heq]
          funext x
          have := snoc_last D g' (List.ofFn x)
          rw [List.length_ofFn] at this
          rw [this]
        · rw [wf_snoc_out gs g i h]; exact Or.inl ⟨false, rfl⟩

lemma small (f : (Fin 6 → Bool) → Bool) (D : List Gate) (hD : Ok D) (hlen : D.length ≤ 7)
    (h : Realized f D) : HasCircuitSize 6 f 7 := by
  rcases h with ⟨b, rfl⟩ | ⟨k, -, rfl⟩
  · cases b
    · refine ⟨⟨[], 6⟩, fun g hg => by simp at hg, by simp [Circuit.size], fun x => ?_⟩
      simp [Circuit.eval, Circuit.wires, List.getD_eq_getElem?_getD]
    · refine ⟨⟨[⟨GateOp.and, []⟩], 6⟩, ?_, by simp [Circuit.size], fun x => ?_⟩
      · intro g hg
        simp only [List.mem_singleton] at hg
        subst hg
        simp
      · simp [Circuit.eval, Circuit.wires, List.getD_eq_getElem?_getD, GateOp.eval]
  · exact ⟨⟨D, k⟩, hD, hlen, fun x => rfl⟩

lemma pick (c : Circuit) (hsize : c.size = 11) (hc : 8 ≤ (T c.gates).card) :
    ∃ t : Fin 8 → Fin 11,
      (∀ i j, i ≠ j → ∃ x, (c.wires (row x)).getD (7 + (t i).val) false ≠
        (c.wires (row x)).getD (7 + (t j).val) false) ∧
      ∀ i (r : Fin 8), ∃ x, (c.wires (row x)).getD (7 + (t i).val) false ≠
        (false :: true :: List.ofFn x).getD r.val false := by
  have hlen : c.gates.length = 11 := hsize
  have key : ∀ f ∈ T c.gates, ∃ j : Fin 11, wf c.gates (7 + j.val) = f := by
    intro f hf
    simp only [T, Finset.mem_filter, Finset.mem_image, Finset.mem_range] at hf
    obtain ⟨⟨i, hi, rfl⟩, hn⟩ := hf
    by_cases h7 : 7 ≤ i
    · refine ⟨⟨i - 7, by omega⟩, ?_⟩
      show wf c.gates (7 + (i - 7)) = wf c.gates i
      congr 1
      omega
    · exfalso
      have hw : ∀ x, wf c.gates i x = (row x).getD i false :=
        fun x => run_getD _ _ _ (by simp [row]; omega)
      have hi7 : i < 7 := by omega
      interval_cases i
      · obtain ⟨x, hx⟩ := hn 2; exact hx (by rw [hw]; rfl)
      · obtain ⟨x, hx⟩ := hn 3; exact hx (by rw [hw]; rfl)
      · obtain ⟨x, hx⟩ := hn 0; exact hx (by rw [hw]; rfl)
      · obtain ⟨x, hx⟩ := hn 4; exact hx (by rw [hw]; rfl)
      · obtain ⟨x, hx⟩ := hn 5; exact hx (by rw [hw]; rfl)
      · obtain ⟨x, hx⟩ := hn 6; exact hx (by rw [hw]; rfl)
      · obtain ⟨x, hx⟩ := hn 7; exact hx (by rw [hw]; rfl)
  let e : Fin 8 ↪ T c.gates := (Fin.castLEEmb hc).trans (T c.gates).equivFin.symm.toEmbedding
  choose j hj using fun a : Fin 8 => key (e a).1 (e a).2
  refine ⟨j, ?_, ?_⟩
  · intro a b hab
    by_contra hcon
    push Not at hcon
    have h3 : wf c.gates (7 + (j a).val) = wf c.gates (7 + (j b).val) := funext hcon
    rw [hj a, hj b] at h3
    exact hab (e.injective (Subtype.ext h3))
  · intro a r
    obtain ⟨x, hx⟩ := (Finset.mem_filter.mp (e a).2).2 r
    refine ⟨x, ?_⟩
    show wf c.gates (7 + (j a).val) x ≠ _
    rw [congrFun (hj a) x]
    exact hx

end PEqualNP.Outside.L_meta_4356

theorem PEqualNP.Outside.L_meta_4356 : have x1 : (Fin (6 : ℕ) → Bool) → List Bool := fun (x1 : Fin (6 : ℕ) → Bool) => [x1 (0 : Fin (6 : ℕ)), x1 (1 : Fin (6 : ℕ)), Bool.false, x1 (2 : Fin (6 : ℕ)), x1 (3 : Fin (6 : ℕ)), x1 (4 : Fin (6 : ℕ)), x1 (5 : Fin (6 : ℕ))]; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.FanInTwo x2 →     x2.size = (11 : ℕ) →       PEqualNP.MetaComplexity.HasCircuitSize (6 : ℕ) (fun (x5 : Fin (6 : ℕ) → Bool) => x2.eval (x1 x5)) (7 : ℕ) ∨         have x5 : Fin (11 : ℕ) → (Fin (6 : ℕ) → Bool) → Bool := fun (x5 : Fin (11 : ℕ)) (x6 : Fin (6 : ℕ) → Bool) => (x2.wires (x1 x6)).getD ((7 : ℕ) + ↑x5) Bool.false;         ∃ (x6 : Fin (8 : ℕ) → Fin (11 : ℕ)), (∀ (x7 x8 : Fin (8 : ℕ)), x7 ≠ x8 → ∃ (x10 : Fin (6 : ℕ) → Bool), x5 (x6 x7) x10 ≠ x5 (x6 x8) x10) ∧ ∀ (x7 x8 : Fin (8 : ℕ)), ∃ (x9 : Fin (6 : ℕ) → Bool), x5 (x6 x7) x9 ≠ (Bool.false :: Bool.true :: List.ofFn x9).getD (↑x8) Bool.false := by
  dsimp only
  intro c hfan hsize
  obtain ⟨D, hD, hlen, hR⟩ := PEqualNP.Outside.L_meta_4356.main c.gates hfan
  by_cases hc : (PEqualNP.Outside.L_meta_4356.T c.gates).card ≤ 7
  · left
    exact PEqualNP.Outside.L_meta_4356.small _ D hD (hlen.trans hc) (hR c.output)
  · right
    exact PEqualNP.Outside.L_meta_4356.pick c hsize (by omega)
