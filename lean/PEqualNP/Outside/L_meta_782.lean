import Mathlib.Data.Finset.Max
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_782

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

lemma fold_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, gs.foldl step w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp, rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (step w g)
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    rw [List.foldl_cons, ht]
    simp [step]

lemma fold_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := fold_prefix gs w
  rw [ht]
  simp [hl]

lemma fold_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := fold_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

lemma wires_length (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.gates.length := fold_length C.gates x

lemma wires_input (C : Circuit) (x : List Bool) (i : ℕ) (h : i < x.length) :
    (C.wires x).getD i false = x.getD i false := fold_getD_lt C.gates x i h

def rd (C : Circuit) (x : List Bool) (g i : ℕ) : Bool :=
  if i < g then (C.wires x).getD i false else false

lemma wires_gate (C : Circuit) (x : List Bool) (j : ℕ) (hj : j < C.gates.length) :
    (C.wires x).getD (x.length + j) false =
      C.gates[j].op.eval (C.gates[j].inputs.map fun i => rd C x (x.length + j) i) := by
  have hsplit : C.gates = C.gates.take j ++ C.gates[j] :: C.gates.drop (j + 1) := by
    simp
  set A := (C.gates.take j).foldl step x with hA
  have hAl : A.length = x.length + j := by
    rw [hA, fold_length]
    simp
    omega
  have hw : C.wires x = (C.gates.drop (j + 1)).foldl step (step A C.gates[j]) := by
    rw [wires_eq]
    conv_lhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_cons]
  have hreadA : ∀ i, A.getD i false = rd C x (x.length + j) i := by
    intro i
    unfold rd
    by_cases hi : i < x.length + j
    · simp only [hi, ↓reduceIte]
      rw [hw, fold_getD_lt _ (step A C.gates[j]) i (by simp [step]; omega), step,
        List.getD_append _ _ _ _ (by omega)]
    · simp only [hi, ↓reduceIte]
      rw [List.getD_eq_default]
      omega
  rw [hw, fold_getD_lt _ _ _ (by simp [step]; omega), step,
    List.getD_append_right _ _ _ _ (by omega)]
  simp only [hAl, Nat.sub_self, List.getD_cons_zero]
  congr 1
  exact List.map_congr_left (fun i _ => hreadA i)

def LeL (a b : List Bool) : Prop := ∀ i, a.getD i false = true → b.getD i false = true

lemma eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (l : List ℕ)
    (f f' : ℕ → Bool) (h : ∀ i, f i = true → f' i = true) :
    op.eval (l.map f) = true → op.eval (l.map f') = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true, List.mem_map, id]
    intro H x hx
    obtain ⟨i, hi, rfl⟩ := hx
    exact h i (H (f i) ⟨i, hi, rfl⟩)
  · simp only [GateOp.eval, List.any_eq_true, List.mem_map, id]
    rintro ⟨x, ⟨i, hi, rfl⟩, hx⟩
    exact ⟨f' i, ⟨i, hi, rfl⟩, h i hx⟩

lemma fold_mono (gs : List Gate) (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ a b : List Bool, a.length = b.length → LeL a b →
      LeL (gs.foldl step a) (gs.foldl step b) := by
  induction gs with
  | nil => intro a b _ h; exact h
  | cons g gs ih =>
    intro a b hl h
    rw [List.foldl_cons, List.foldl_cons]
    apply ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg'))
    · simp [step, hl]
    · intro i hi
      unfold step at hi ⊢
      by_cases hia : i < a.length
      · rw [List.getD_append _ _ _ _ hia] at hi
        rw [List.getD_append _ _ _ _ (by omega)]
        exact h i hi
      · rw [List.getD_append_right _ _ _ _ (by omega)] at hi
        rw [List.getD_append_right _ _ _ _ (by omega), ← hl]
        by_cases he : i - a.length = 0
        · rw [he] at hi ⊢
          simp only [List.getD_cons_zero] at hi ⊢
          exact eval_mono g.op (hgs g List.mem_cons_self) _ _ _ (fun k => h k) hi
        · obtain ⟨m, hm⟩ : ∃ m, i - a.length = m + 1 := ⟨i - a.length - 1, by omega⟩
          rw [hm] at hi
          simp at hi

lemma wires_mono (C : Circuit) (hC : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (a b : List Bool) (hl : a.length = b.length) (h : LeL a b) : LeL (C.wires a) (C.wires b) :=
  fold_mono C.gates hC a b hl h

def val (C : Circuit) {n : ℕ} (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

def supp (C : Circuit) (n w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun a : Fin n =>
    (C.wires (List.ofFn (fun b : Fin n => decide (b = a)))).getD w false = true)

lemma getD_ofFn {n : ℕ} (x : Fin n → Bool) (i : ℕ) :
    (List.ofFn x).getD i false = if h : i < n then x ⟨i, h⟩ else false := by
  by_cases h : i < n
  · simp only [h, ↓reduceDIte]
    rw [List.getD_eq_getElem?_getD]
    simp [h]
  · simp only [h, ↓reduceDIte]
    rw [List.getD_eq_default]
    simp
    omega

lemma val_mono (C : Circuit) (hC : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    {n : ℕ} (x y : Fin n → Bool) (hxy : ∀ q : Fin n, x q = true → y q = true) (w : ℕ) :
    val C x w = true → val C y w = true := by
  apply wires_mono C hC (List.ofFn x) (List.ofFn y) (by simp)
  intro i hi
  rw [getD_ofFn] at hi ⊢
  by_cases h : i < n
  · simp only [h, ↓reduceDIte] at hi ⊢
    exact hxy ⟨i, h⟩ hi
  · simp only [h, ↓reduceDIte] at hi
    cases hi

lemma list_len2 (l : List ℕ) (h : l.length = 2) : l = [l.getD 0 0, l.getD 1 0] := by
  rcases l with _ | ⟨a, _ | ⟨b, _ | _⟩⟩ <;> simp at h ⊢

lemma val_gate_and {n : ℕ} (C : Circuit)
    (hC : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (j : ℕ) (hj : j < C.gates.length) (hop : C.gates[j].op = GateOp.and) (x : Fin n → Bool) :
    val C x (n + j) =
      ((if C.gates[j].inputs.getD 0 0 < n + j then val C x (C.gates[j].inputs.getD 0 0) else false) &&
       (if C.gates[j].inputs.getD 1 0 < n + j then val C x (C.gates[j].inputs.getD 1 0) else false)) := by
  have hlen : C.gates[j].inputs.length = 2 := (hC _ (List.getElem_mem hj)).2
  have hg := wires_gate C (List.ofFn x) j hj
  simp only [List.length_ofFn] at hg
  change val C x (n + j) = _ at hg
  rw [hg, hop]
  conv_lhs => rw [list_len2 C.gates[j].inputs hlen]
  simp [GateOp.eval, rd, val]

lemma val_gate_or {n : ℕ} (C : Circuit)
    (hC : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (j : ℕ) (hj : j < C.gates.length) (hop : C.gates[j].op = GateOp.or) (x : Fin n → Bool) :
    val C x (n + j) =
      ((if C.gates[j].inputs.getD 0 0 < n + j then val C x (C.gates[j].inputs.getD 0 0) else false) ||
       (if C.gates[j].inputs.getD 1 0 < n + j then val C x (C.gates[j].inputs.getD 1 0) else false)) := by
  have hlen : C.gates[j].inputs.length = 2 := (hC _ (List.getElem_mem hj)).2
  have hg := wires_gate C (List.ofFn x) j hj
  simp only [List.length_ofFn] at hg
  change val C x (n + j) = _ at hg
  rw [hg, hop]
  conv_lhs => rw [list_len2 C.gates[j].inputs hlen]
  simp [GateOp.eval, rd, val]

lemma supp_lt (C : Circuit) (n w : ℕ) (hw : w < n) : (supp C n w).card ≤ 1 := by
  have hsub : supp C n w ⊆ {⟨w, hw⟩} := by
    intro a ha
    rw [supp, Finset.mem_filter] at ha
    have hwa : (C.wires (List.ofFn (fun b : Fin n => decide (b = a)))).getD w false =
        (List.ofFn (fun b : Fin n => decide (b = a))).getD w false :=
      wires_input C _ w (by simp; exact hw)
    rw [hwa, getD_ofFn] at ha
    simp only [hw, ↓reduceDIte] at ha
    simp only [Finset.mem_singleton]
    exact (decide_eq_true_eq.mp ha.2).symm
  exact (Finset.card_le_card hsub).trans (by simp)

lemma supp_ge (C : Circuit) (n w : ℕ) (hw : n + C.gates.length ≤ w) : supp C n w = ∅ := by
  ext a
  simp only [supp, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
  rw [List.getD_eq_default]
  · simp
  · rw [wires_length]; simp; omega

lemma supp_and_children {n : ℕ} (C : Circuit)
    (hC : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (j : ℕ) (hj : j < C.gates.length) (hop : C.gates[j].op = GateOp.and)
    (hne : (supp C n (n + j)).Nonempty) :
    C.gates[j].inputs.getD 0 0 < n + j ∧
    C.gates[j].inputs.getD 1 0 < n + j ∧
    supp C n (n + j) ⊆ supp C n (C.gates[j].inputs.getD 0 0) ∧
    supp C n (n + j) ⊆ supp C n (C.gates[j].inputs.getD 1 0) := by
  obtain ⟨a0, ha0⟩ := hne
  rw [supp, Finset.mem_filter] at ha0
  have h0 : val C (fun b : Fin n => decide (b = a0)) (n + j) = true := ha0.2
  rw [val_gate_and C hC j hj hop] at h0
  simp only [Bool.and_eq_true] at h0
  have hu : C.gates[j].inputs.getD 0 0 < n + j := by
    by_contra hc
    have h01 := h0.1
    simp only [hc, ↓reduceIte] at h01
    cases h01
  have hv : C.gates[j].inputs.getD 1 0 < n + j := by
    by_contra hc
    have h02 := h0.2
    simp only [hc, ↓reduceIte] at h02
    cases h02
  refine ⟨hu, hv, ?_, ?_⟩
  · intro a ha
    rw [supp, Finset.mem_filter] at ha ⊢
    refine ⟨Finset.mem_univ a, ?_⟩
    have hval : val C (fun b : Fin n => decide (b = a)) (n + j) = true := ha.2
    rw [val_gate_and C hC j hj hop] at hval
    simp only [hu, hv, ↓reduceIte, Bool.and_eq_true] at hval
    exact hval.1
  · intro a ha
    rw [supp, Finset.mem_filter] at ha ⊢
    refine ⟨Finset.mem_univ a, ?_⟩
    have hval : val C (fun b : Fin n => decide (b = a)) (n + j) = true := ha.2
    rw [val_gate_and C hC j hj hop] at hval
    simp only [hu, hv, ↓reduceIte, Bool.and_eq_true] at hval
    exact hval.2

lemma supp_or_biUnion {n : ℕ} (C : Circuit)
    (hC : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (j : ℕ) (hj : j < C.gates.length) (hop : C.gates[j].op = GateOp.or) :
    supp C n (n + j) ⊆
      (({C.gates[j].inputs.getD 0 0, C.gates[j].inputs.getD 1 0} : Finset ℕ).filter (· < n + j)).biUnion
        (supp C n) := by
  intro a ha
  rw [supp, Finset.mem_filter] at ha
  have hval : val C (fun b : Fin n => decide (b = a)) (n + j) = true := ha.2
  rw [val_gate_or C hC j hj hop, Bool.or_eq_true] at hval
  rw [Finset.mem_biUnion]
  rcases hval with h1 | h2
  · split_ifs at h1 with hu
    refine ⟨C.gates[j].inputs.getD 0 0, Finset.mem_filter.mpr ⟨by simp, hu⟩, ?_⟩
    rw [supp, Finset.mem_filter]
    exact ⟨Finset.mem_univ a, h1⟩
  · split_ifs at h2 with hv
    refine ⟨C.gates[j].inputs.getD 1 0, Finset.mem_filter.mpr ⟨by simp, hv⟩, ?_⟩
    rw [supp, Finset.mem_filter]
    exact ⟨Finset.mem_univ a, h2⟩

def privGates (C : Circuit) (n : ℕ) (Si : Finset (Fin n)) : Finset (Fin C.gates.length) :=
  Finset.univ.filter (fun j : Fin C.gates.length =>
    2 ≤ (supp C n (n + j.val)).card ∧ supp C n (n + j.val) ⊆ Si)

def privWires (C : Circuit) (n : ℕ) (Si : Finset (Fin n)) : Finset ℕ :=
  (privGates C n Si).image (fun j => n + j.val)

lemma privWires_card (C : Circuit) (n : ℕ) (Si : Finset (Fin n)) :
    (privWires C n Si).card = (privGates C n Si).card := by
  apply Finset.card_image_of_injective
  intro a b hab
  dsimp only at hab
  exact Fin.ext (by omega)

lemma mem_privWires_iff (C : Circuit) (n : ℕ) (Si : Finset (Fin n)) (w : ℕ) :
    w ∈ privWires C n Si ↔ 2 ≤ (supp C n w).card ∧ supp C n w ⊆ Si := by
  constructor
  · intro hw
    rw [privWires, Finset.mem_image] at hw
    obtain ⟨j, hj, rfl⟩ := hw
    rw [privGates, Finset.mem_filter] at hj
    exact hj.2
  · rintro ⟨hcard, hsub⟩
    have hn : n ≤ w := by
      by_contra hlt
      have := supp_lt C n w (by omega)
      omega
    have hlt : w < n + C.gates.length := by
      by_contra hge
      have := supp_ge C n w (by omega)
      rw [this] at hcard
      simp at hcard
    rw [privWires, Finset.mem_image]
    refine ⟨⟨w - n, by omega⟩, ?_, by dsimp only; omega⟩
    rw [privGates, Finset.mem_filter]
    have hw : n + (w - n) = w := by omega
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [hw]
    exact ⟨hcard, hsub⟩

def lbl (C : Circuit) (n : ℕ) (Si : Finset (Fin n)) (w : ℕ) : Bool :=
  if h : n ≤ w ∧ w - n < C.gates.length ∧ 2 ≤ (supp C n w).card ∧ supp C n w ⊆ Si then
    let g := C.gates[w - n]'h.2.1
    let u := g.inputs.getD 0 0
    let v := g.inputs.getD 1 0
    let lu := if _hu : u < w then lbl C n Si u else false
    let lv := if _hv : v < w then lbl C n Si v else false
    match g.op with
    | GateOp.and => lu && lv
    | GateOp.or => lu || lv
    | _ => decide (¬ supp C n w ⊆ Si)
  else
    decide (¬ supp C n w ⊆ Si)
termination_by w

lemma lbl_exit (C : Circuit) (n : ℕ) (Si : Finset (Fin n)) (w : ℕ)
    (hw : w ∉ privWires C n Si) :
    lbl C n Si w = decide (¬ supp C n w ⊆ Si) := by
  have hneg : ¬ (n ≤ w ∧ w - n < C.gates.length ∧ 2 ≤ (supp C n w).card ∧ supp C n w ⊆ Si) := by
    rintro ⟨_, _, h1, h2⟩
    exact hw ((mem_privWires_iff C n Si w).mpr ⟨h1, h2⟩)
  rw [lbl]
  simp [hneg]

lemma lbl_priv_and (C : Circuit) (n : ℕ) (Si : Finset (Fin n)) (j : ℕ)
    (hj : j < C.gates.length) (hw : n + j ∈ privWires C n Si)
    (hop : C.gates[j].op = GateOp.and) :
    lbl C n Si (n + j) =
      ((if C.gates[j].inputs.getD 0 0 < n + j then lbl C n Si (C.gates[j].inputs.getD 0 0) else false) &&
       (if C.gates[j].inputs.getD 1 0 < n + j then lbl C n Si (C.gates[j].inputs.getD 1 0) else false)) := by
  obtain ⟨h1, h2⟩ := (mem_privWires_iff C n Si (n + j)).mp hw
  have hpos : n ≤ n + j ∧ (n + j) - n < C.gates.length ∧ 2 ≤ (supp C n (n + j)).card ∧ supp C n (n + j) ⊆ Si :=
    ⟨Nat.le_add_right n j, by omega, h1, h2⟩
  rw [lbl]
  simp only [eq_true hpos, ↓reduceDIte]
  have heq : (n + j) - n = j := by omega
  simp only [heq, hop, dite_eq_ite]

lemma lbl_priv_or (C : Circuit) (n : ℕ) (Si : Finset (Fin n)) (j : ℕ)
    (hj : j < C.gates.length) (hw : n + j ∈ privWires C n Si)
    (hop : C.gates[j].op = GateOp.or) :
    lbl C n Si (n + j) =
      ((if C.gates[j].inputs.getD 0 0 < n + j then lbl C n Si (C.gates[j].inputs.getD 0 0) else false) ||
       (if C.gates[j].inputs.getD 1 0 < n + j then lbl C n Si (C.gates[j].inputs.getD 1 0) else false)) := by
  obtain ⟨h1, h2⟩ := (mem_privWires_iff C n Si (n + j)).mp hw
  have hpos : n ≤ n + j ∧ (n + j) - n < C.gates.length ∧ 2 ≤ (supp C n (n + j)).card ∧ supp C n (n + j) ⊆ Si :=
    ⟨Nat.le_add_right n j, by omega, h1, h2⟩
  rw [lbl]
  simp only [eq_true hpos, ↓reduceDIte]
  have heq : (n + j) - n = j := by omega
  simp only [heq, hop, dite_eq_ite]

lemma frontier_exit_aux
    (P : Finset ℕ)
    (Good : Finset ℕ → Prop)
    (stepFn : ℕ → Finset ℕ)
    (hstep_lt : ∀ w ∈ P, ∀ a ∈ stepFn w, a < w)
    (hstep_card : ∀ w ∈ P, (stepFn w).card ≤ 2)
    (hgood_step : ∀ F : Finset ℕ, ∀ w ∈ F, w ∈ P → Good F → Good (F.erase w ∪ stepFn w)) :
    ∀ (k : ℕ) (F G : Finset ℕ),
      G ⊆ P →
      (∀ x ∈ F ∩ P, ∀ g ∈ G, x < g) →
      F.card ≤ 1 + G.card →
      Good F →
      (P \ G).card ≤ k →
      ∃ E : Finset ℕ, (∀ e ∈ E, e ∉ P) ∧ E.card ≤ 1 + P.card ∧ Good E := by
  intro k
  induction k with
  | zero =>
    intro F G hGP hord hcard hGood hk
    have hPG : P \ G = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hk)
    have hno : ∀ e ∈ F, e ∉ P := by
      intro e he heP
      have heG : e ∉ G := fun hg => lt_irrefl e (hord e (Finset.mem_inter.mpr ⟨he, heP⟩) e hg)
      have hePG : e ∈ P \ G := Finset.mem_sdiff.mpr ⟨heP, heG⟩
      rw [hPG] at hePG
      exact Finset.notMem_empty e hePG
    exact ⟨F, hno, hcard.trans (Nat.add_le_add_left (Finset.card_le_card hGP) 1), hGood⟩
  | succ k ih =>
    intro F G hGP hord hcard hGood hk
    by_cases hne : (F ∩ P).Nonempty
    · let w := (F ∩ P).max' hne
      have hw_inter : w ∈ F ∩ P := Finset.max'_mem (F ∩ P) hne
      have hwF : w ∈ F := (Finset.mem_inter.mp hw_inter).1
      have hwP : w ∈ P := (Finset.mem_inter.mp hw_inter).2
      have hwG : w ∉ G := fun hg => lt_irrefl w (hord w hw_inter w hg)
      let F' := F.erase w ∪ stepFn w
      let G' := insert w G
      have hGP' : G' ⊆ P := Finset.insert_subset_iff.mpr ⟨hwP, hGP⟩
      have hord' : ∀ x ∈ F' ∩ P, ∀ g ∈ G', x < g := by
        intro x hx g hg
        rw [Finset.mem_inter, Finset.mem_union] at hx
        have hxltw : x < w := by
          rcases hx.1 with hx1 | hx2
          · obtain ⟨hxne, hxF⟩ := Finset.mem_erase.mp hx1
            have hxle := Finset.le_max' (F ∩ P) x (Finset.mem_inter.mpr ⟨hxF, hx.2⟩)
            exact lt_of_le_of_ne hxle hxne
          · exact hstep_lt w hwP x hx2
        rcases Finset.mem_insert.mp hg with rfl | hgG
        · exact hxltw
        · exact lt_trans hxltw (hord w hw_inter g hgG)
      have hcard' : F'.card ≤ 1 + G'.card := by
        have h1 : F'.card ≤ (F.erase w).card + (stepFn w).card := Finset.card_union_le _ _
        have h2 : (F.erase w).card = F.card - 1 := Finset.card_erase_of_mem hwF
        have h3 : (stepFn w).card ≤ 2 := hstep_card w hwP
        have h4 : 1 ≤ F.card := Finset.card_pos.mpr ⟨w, hwF⟩
        have h5 : G'.card = G.card + 1 := Finset.card_insert_of_notMem hwG
        omega
      have hGood' : Good F' := hgood_step F w hwF hwP hGood
      have hk' : (P \ G').card ≤ k := by
        have heq : P \ G' = (P \ G).erase w := by
          ext a
          simp only [G', Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase]
          tauto
        have hwPG : w ∈ P \ G := Finset.mem_sdiff.mpr ⟨hwP, hwG⟩
        rw [heq, Finset.card_erase_of_mem hwPG]
        omega
      exact ih F' G' hGP' hord' hcard' hGood' hk'
    · have hno : ∀ e ∈ F, e ∉ P := fun e he heP => hne ⟨e, Finset.mem_inter.mpr ⟨he, heP⟩⟩
      exact ⟨F, hno, hcard.trans (Nat.add_le_add_left (Finset.card_le_card hGP) 1), hGood⟩

lemma frontier_exit
    (P : Finset ℕ)
    (Good : Finset ℕ → Prop)
    (stepFn : ℕ → Finset ℕ)
    (hstep_lt : ∀ w ∈ P, ∀ a ∈ stepFn w, a < w)
    (hstep_card : ∀ w ∈ P, (stepFn w).card ≤ 2)
    (hgood_step : ∀ F : Finset ℕ, ∀ w ∈ F, w ∈ P → Good F → Good (F.erase w ∪ stepFn w))
    (r : ℕ) (hr : Good {r}) :
    ∃ E : Finset ℕ, (∀ e ∈ E, e ∉ P) ∧ E.card ≤ 1 + P.card ∧ Good E := by
  refine frontier_exit_aux P Good stepFn hstep_lt hstep_card hgood_step P.card {r} ∅
    (Finset.empty_subset P) ?_ (by simp) hr (by simp)
  intro x _ g hg
  exact absurd hg (Finset.notMem_empty g)

def stepTrue (C : Circuit) (n : ℕ) (Si : Finset (Fin n)) (w : ℕ) : Finset ℕ :=
  if h : n ≤ w ∧ w - n < C.gates.length then
    let g := C.gates[w - n]'h.2
    let u := g.inputs.getD 0 0
    let v := g.inputs.getD 1 0
    match g.op with
    | GateOp.and => ({u, v} : Finset ℕ).filter (· < w)
    | GateOp.or =>
      if u < w ∧ lbl C n Si u = true then {u}
      else if v < w ∧ lbl C n Si v = true then {v}
      else ∅
    | _ => ∅
  else ∅

lemma stepTrue_and (C : Circuit) (n : ℕ) (Si : Finset (Fin n)) (j : ℕ)
    (hj : j < C.gates.length) (hop : C.gates[j].op = GateOp.and) :
    stepTrue C n Si (n + j) =
      ({C.gates[j].inputs.getD 0 0, C.gates[j].inputs.getD 1 0} : Finset ℕ).filter (· < n + j) := by
  unfold stepTrue
  split_ifs with h
  · simp only [Nat.add_sub_cancel_left, hop]
  · exfalso; exact h ⟨Nat.le_add_right n j, by omega⟩

lemma stepTrue_or (C : Circuit) (n : ℕ) (Si : Finset (Fin n)) (j : ℕ)
    (hj : j < C.gates.length) (hop : C.gates[j].op = GateOp.or) :
    stepTrue C n Si (n + j) =
      if C.gates[j].inputs.getD 0 0 < n + j ∧ lbl C n Si (C.gates[j].inputs.getD 0 0) = true then
        {C.gates[j].inputs.getD 0 0}
      else if C.gates[j].inputs.getD 1 0 < n + j ∧ lbl C n Si (C.gates[j].inputs.getD 1 0) = true then
        {C.gates[j].inputs.getD 1 0}
      else ∅ := by
  have hcond : n ≤ n + j ∧ j < C.gates.length := ⟨Nat.le_add_right n j, hj⟩
  unfold stepTrue
  simp only [Nat.add_sub_cancel_left, hop]
  simp only [eq_true hcond, ↓reduceDIte]

lemma stepTrue_lt (C : Circuit) (n : ℕ) (Si : Finset (Fin n)) (w : ℕ) :
    ∀ a ∈ stepTrue C n Si w, a < w := by
  intro a ha
  unfold stepTrue at ha
  split_ifs at ha with h
  · cases hop : (C.gates[w - n]'h.2).op <;> simp only [hop] at ha
    · exact (Finset.mem_filter.mp ha).2
    · split_ifs at ha with h1 h2
      · simp only [Finset.mem_singleton] at ha; subst ha; exact h1.1
      · simp only [Finset.mem_singleton] at ha; subst ha; exact h2.1
      · exact absurd ha (Finset.notMem_empty a)
    · exact absurd ha (Finset.notMem_empty a)
    · exact absurd ha (Finset.notMem_empty a)
    · exact absurd ha (Finset.notMem_empty a)
  · exact absurd ha (Finset.notMem_empty a)

lemma stepTrue_card (C : Circuit) (n : ℕ) (Si : Finset (Fin n)) (w : ℕ) :
    (stepTrue C n Si w).card ≤ 2 := by
  unfold stepTrue
  split_ifs with h
  · cases hop : (C.gates[w - n]'h.2).op <;> simp only [hop]
    · exact (Finset.card_filter_le _ _).trans ((Finset.card_insert_le _ _).trans (by simp))
    · split_ifs <;> simp
    · simp
    · simp
    · simp
  · simp

lemma case_true {n k : ℕ} (Si : Finset (Fin n)) (C : Circuit) (oi c_i : ℕ)
    (hC : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (hprom : ∀ x : Fin n → Bool, (Finset.univ.filter (fun q : Fin n => x q = true)).card ≤ k →
      (∀ q ∈ Si, x q = false) → val C x oi = false)
    (hc_k : c_i ≤ k)
    (hlbl : lbl C n Si oi = true) :
    c_i ≤ (privGates C n Si).card := by
  let P := privWires C n Si
  let Good : Finset ℕ → Prop := fun F =>
    (∀ w ∈ F, lbl C n Si w = true) ∧
    (∀ x : Fin n → Bool, (∀ w ∈ F, val C x w = true) → val C x oi = true)
  have hgood_step : ∀ F : Finset ℕ, ∀ w ∈ F, w ∈ P → Good F →
      Good (F.erase w ∪ stepTrue C n Si w) := by
    intro F w hwF hwP hGF
    have hnw : n ≤ w := by
      by_contra hlt
      have hcard := (mem_privWires_iff C n Si w).mp hwP |>.1
      have := supp_lt C n w (by omega)
      omega
    have hjw : w - n < C.gates.length := by
      by_contra hge
      have hcard := (mem_privWires_iff C n Si w).mp hwP |>.1
      have := supp_ge C n w (by omega)
      rw [this] at hcard
      simp at hcard
    obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
    have hjw' : j < C.gates.length := by omega
    have hlblw : lbl C n Si (n + j) = true := hGF.1 (n + j) hwF
    have hgop : C.gates[j].op = GateOp.and ∨ C.gates[j].op = GateOp.or :=
      (hC C.gates[j] (List.getElem_mem hjw')).1
    rcases hgop with hop | hop
    · rw [lbl_priv_and C n Si j hjw' hwP hop, Bool.and_eq_true] at hlblw
      have hu : C.gates[j].inputs.getD 0 0 < n + j ∧
          lbl C n Si (C.gates[j].inputs.getD 0 0) = true := by
        by_cases h1 : C.gates[j].inputs.getD 0 0 < n + j
        · have h1' := hlblw.1
          simp only [h1, ↓reduceIte] at h1'
          exact ⟨h1, h1'⟩
        · have h1' := hlblw.1
          simp only [h1, ↓reduceIte] at h1'
          cases h1'
      have hv : C.gates[j].inputs.getD 1 0 < n + j ∧
          lbl C n Si (C.gates[j].inputs.getD 1 0) = true := by
        by_cases h2 : C.gates[j].inputs.getD 1 0 < n + j
        · have h2' := hlblw.2
          simp only [h2, ↓reduceIte] at h2'
          exact ⟨h2, h2'⟩
        · have h2' := hlblw.2
          simp only [h2, ↓reduceIte] at h2'
          cases h2'
      have hstep := stepTrue_and C n Si j hjw' hop
      refine ⟨?_, ?_⟩
      · intro a ha
        rcases Finset.mem_union.mp ha with ha1 | ha2
        · exact hGF.1 a (Finset.mem_erase.mp ha1).2
        · rw [hstep, Finset.mem_filter] at ha2
          rcases Finset.mem_insert.mp ha2.1 with rfl | ha2'
          · exact hu.2
          · rw [Finset.mem_singleton] at ha2'
            rw [ha2']
            exact hv.2
      · intro x hx
        apply hGF.2 x
        intro a haF
        by_cases haw : a = n + j
        · subst haw
          have hu_mem : C.gates[j].inputs.getD 0 0 ∈ stepTrue C n Si (n + j) := by
            rw [hstep, Finset.mem_filter]
            exact ⟨by simp, hu.1⟩
          have hv_mem : C.gates[j].inputs.getD 1 0 ∈ stepTrue C n Si (n + j) := by
            rw [hstep, Finset.mem_filter]
            exact ⟨by simp, hv.1⟩
          have hxu : val C x (C.gates[j].inputs.getD 0 0) = true :=
            hx _ (Finset.mem_union_right _ hu_mem)
          have hxv : val C x (C.gates[j].inputs.getD 1 0) = true :=
            hx _ (Finset.mem_union_right _ hv_mem)
          rw [val_gate_and C hC j hjw' hop x]
          simp only [hu.1, hv.1, ↓reduceIte, hxu, hxv, Bool.and_self]
        · exact hx a (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨haw, haF⟩))
    · rw [lbl_priv_or C n Si j hjw' hwP hop, Bool.or_eq_true] at hlblw
      have hor : (C.gates[j].inputs.getD 0 0 < n + j ∧ lbl C n Si (C.gates[j].inputs.getD 0 0) = true) ∨
          (C.gates[j].inputs.getD 1 0 < n + j ∧ lbl C n Si (C.gates[j].inputs.getD 1 0) = true) := by
        rcases hlblw with h1 | h2
        · by_cases h1' : C.gates[j].inputs.getD 0 0 < n + j
          · simp only [h1', ↓reduceIte] at h1
            exact Or.inl ⟨h1', h1⟩
          · simp only [h1', ↓reduceIte] at h1
            cases h1
        · by_cases h2' : C.gates[j].inputs.getD 1 0 < n + j
          · simp only [h2', ↓reduceIte] at h2
            exact Or.inr ⟨h2', h2⟩
          · simp only [h2', ↓reduceIte] at h2
            cases h2
      have hstep := stepTrue_or C n Si j hjw' hop
      refine ⟨?_, ?_⟩
      · intro a ha
        rcases Finset.mem_union.mp ha with ha1 | ha2
        · exact hGF.1 a (Finset.mem_erase.mp ha1).2
        · rw [hstep] at ha2
          split_ifs at ha2 with h1 h2
          · rw [Finset.mem_singleton] at ha2; rw [ha2]; exact h1.2
          · rw [Finset.mem_singleton] at ha2; rw [ha2]; exact h2.2
          · exact absurd ha2 (Finset.notMem_empty a)
      · intro x hx
        apply hGF.2 x
        intro a haF
        by_cases haw : a = n + j
        · subst haw
          rw [val_gate_or C hC j hjw' hop x]
          by_cases h1 : C.gates[j].inputs.getD 0 0 < n + j ∧
              lbl C n Si (C.gates[j].inputs.getD 0 0) = true
          · have hu_mem : C.gates[j].inputs.getD 0 0 ∈ stepTrue C n Si (n + j) := by
              rw [hstep]
              simp only [eq_true h1, ↓reduceIte, Finset.mem_singleton]
            have hxu : val C x (C.gates[j].inputs.getD 0 0) = true :=
              hx _ (Finset.mem_union_right _ hu_mem)
            simp only [h1.1, ↓reduceIte, hxu, Bool.true_or]
          · have h2 : C.gates[j].inputs.getD 1 0 < n + j ∧
                lbl C n Si (C.gates[j].inputs.getD 1 0) = true := by
              rcases hor with hu' | hv'
              · exact absurd hu' h1
              · exact hv'
            have hv_mem : C.gates[j].inputs.getD 1 0 ∈ stepTrue C n Si (n + j) := by
              rw [hstep]
              simp only [eq_false h1, eq_true h2, ↓reduceIte, Finset.mem_singleton]
            have hxv : val C x (C.gates[j].inputs.getD 1 0) = true :=
              hx _ (Finset.mem_union_right _ hv_mem)
            simp only [h2.1, ↓reduceIte, hxv, Bool.or_true]
        · exact hx a (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨haw, haF⟩))
  obtain ⟨E, hE_out, hE_card, hGE⟩ := frontier_exit P Good (stepTrue C n Si)
    (fun w _ a ha => stepTrue_lt C n Si w a ha)
    (fun w _ => stepTrue_card C n Si w)
    hgood_step oi ⟨fun w hw => by rw [Finset.mem_singleton.mp hw]; exact hlbl,
      fun x hx => hx oi (Finset.mem_singleton_self oi)⟩
  have hex : ∀ e ∈ E, ∃ q : Fin n, q ∈ supp C n e ∧ q ∉ Si := by
    intro e he
    have hle := hGE.1 e he
    rw [lbl_exit C n Si e (hE_out e he)] at hle
    exact Finset.not_subset.mp (decide_eq_true_eq.mp hle)
  let Q : Finset (Fin n) := E.attach.image (fun e => Classical.choose (hex e.1 e.2))
  let x : Fin n → Bool := fun q => decide (q ∈ Q)
  have hx_filter : Finset.univ.filter (fun q : Fin n => x q = true) = Q := by
    ext q
    simp [x]
  have hx_Si : ∀ q ∈ Si, x q = false := by
    intro q hqSi
    simp only [x, decide_eq_false_iff_not]
    intro hqQ
    rw [Finset.mem_image] at hqQ
    obtain ⟨⟨e, he⟩, _, hqeq⟩ := hqQ
    have hspec := (Classical.choose_spec (hex e he)).2
    rw [hqeq] at hspec
    exact hspec hqSi
  have hx_E : ∀ e ∈ E, val C x e = true := by
    intro e he
    let q := Classical.choose (hex e he)
    have hq_supp : q ∈ supp C n e := (Classical.choose_spec (hex e he)).1
    have hq_Q : q ∈ Q := Finset.mem_image.mpr ⟨⟨e, he⟩, Finset.mem_attach E ⟨e, he⟩, rfl⟩
    rw [supp, Finset.mem_filter] at hq_supp
    have hmono : ∀ b : Fin n, decide (b = q) = true → x b = true := by
      intro b hb
      rw [decide_eq_true_eq] at hb
      subst hb
      simp [x, hq_Q]
    exact val_mono C (fun g hg => (hC g hg).1) _ x hmono e hq_supp.2
  have hx_oi : val C x oi = true := hGE.2 x hx_E
  have hQ_gt : k < Q.card := by
    by_contra hle
    have hk_le : (Finset.univ.filter (fun q : Fin n => x q = true)).card ≤ k := by
      rw [hx_filter]
      omega
    have hfalse := hprom x hk_le hx_Si
    rw [hx_oi] at hfalse
    cases hfalse
  have hQ_le_E : Q.card ≤ E.card := by
    calc Q.card ≤ E.attach.card := Finset.card_image_le
      _ = E.card := Finset.card_attach
  rw [privWires_card] at hE_card
  omega

def stepFalse (C : Circuit) (n : ℕ) (Si : Finset (Fin n)) (w : ℕ) : Finset ℕ :=
  if h : n ≤ w ∧ w - n < C.gates.length then
    let g := C.gates[w - n]'h.2
    let u := g.inputs.getD 0 0
    let v := g.inputs.getD 1 0
    match g.op with
    | GateOp.and =>
      if u < w ∧ lbl C n Si u = false then {u}
      else if v < w ∧ lbl C n Si v = false then {v}
      else ∅
    | GateOp.or => ({u, v} : Finset ℕ).filter (· < w)
    | _ => ∅
  else ∅

lemma stepFalse_and (C : Circuit) (n : ℕ) (Si : Finset (Fin n)) (j : ℕ)
    (hj : j < C.gates.length) (hop : C.gates[j].op = GateOp.and) :
    stepFalse C n Si (n + j) =
      if C.gates[j].inputs.getD 0 0 < n + j ∧ lbl C n Si (C.gates[j].inputs.getD 0 0) = false then
        {C.gates[j].inputs.getD 0 0}
      else if C.gates[j].inputs.getD 1 0 < n + j ∧ lbl C n Si (C.gates[j].inputs.getD 1 0) = false then
        {C.gates[j].inputs.getD 1 0}
      else ∅ := by
  have hcond : n ≤ n + j ∧ j < C.gates.length := ⟨Nat.le_add_right n j, hj⟩
  unfold stepFalse
  simp only [Nat.add_sub_cancel_left, hop]
  simp only [eq_true hcond, ↓reduceDIte]

lemma stepFalse_or (C : Circuit) (n : ℕ) (Si : Finset (Fin n)) (j : ℕ)
    (hj : j < C.gates.length) (hop : C.gates[j].op = GateOp.or) :
    stepFalse C n Si (n + j) =
      ({C.gates[j].inputs.getD 0 0, C.gates[j].inputs.getD 1 0} : Finset ℕ).filter (· < n + j) := by
  unfold stepFalse
  split_ifs with h
  · simp only [Nat.add_sub_cancel_left, hop]
  · exfalso; exact h ⟨Nat.le_add_right n j, by omega⟩

lemma stepFalse_lt (C : Circuit) (n : ℕ) (Si : Finset (Fin n)) (w : ℕ) :
    ∀ a ∈ stepFalse C n Si w, a < w := by
  intro a ha
  unfold stepFalse at ha
  split_ifs at ha with h
  · cases hop : (C.gates[w - n]'h.2).op <;> simp only [hop] at ha
    · split_ifs at ha with h1 h2
      · simp only [Finset.mem_singleton] at ha; subst ha; exact h1.1
      · simp only [Finset.mem_singleton] at ha; subst ha; exact h2.1
      · exact absurd ha (Finset.notMem_empty a)
    · exact (Finset.mem_filter.mp ha).2
    · exact absurd ha (Finset.notMem_empty a)
    · exact absurd ha (Finset.notMem_empty a)
    · exact absurd ha (Finset.notMem_empty a)
  · exact absurd ha (Finset.notMem_empty a)

lemma stepFalse_card (C : Circuit) (n : ℕ) (Si : Finset (Fin n)) (w : ℕ) :
    (stepFalse C n Si w).card ≤ 2 := by
  unfold stepFalse
  split_ifs with h
  · cases hop : (C.gates[w - n]'h.2).op <;> simp only [hop]
    · split_ifs <;> simp
    · exact (Finset.card_filter_le _ _).trans ((Finset.card_insert_le _ _).trans (by simp))
    · simp
    · simp
    · simp
  · simp

lemma case_false {n : ℕ} (Si : Finset (Fin n)) (C : Circuit) (oi c_i : ℕ)
    (hC : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (hc_L : c_i + 1 ≤ (supp C n oi).card)
    (hlbl : lbl C n Si oi = false) :
    c_i ≤ (privGates C n Si).card := by
  let P := privWires C n Si
  let Good : Finset ℕ → Prop := fun F =>
    (∀ w ∈ F, lbl C n Si w = false) ∧ (supp C n oi ⊆ F.biUnion (supp C n))
  have hgood_step : ∀ F : Finset ℕ, ∀ w ∈ F, w ∈ P → Good F →
      Good (F.erase w ∪ stepFalse C n Si w) := by
    intro F w hwF hwP hGF
    have hcardw : 2 ≤ (supp C n w).card := (mem_privWires_iff C n Si w).mp hwP |>.1
    have hnw : n ≤ w := by
      by_contra hlt
      have := supp_lt C n w (by omega)
      omega
    have hjw : w - n < C.gates.length := by
      by_contra hge
      have := supp_ge C n w (by omega)
      rw [this] at hcardw
      simp at hcardw
    obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
    have hjw' : j < C.gates.length := by omega
    have hlblw : lbl C n Si (n + j) = false := hGF.1 (n + j) hwF
    have hgop : C.gates[j].op = GateOp.and ∨ C.gates[j].op = GateOp.or :=
      (hC C.gates[j] (List.getElem_mem hjw')).1
    have hstep_lbl : ∀ a ∈ stepFalse C n Si (n + j), lbl C n Si a = false := by
      intro a ha
      rcases hgop with hop | hop
      · rw [stepFalse_and C n Si j hjw' hop] at ha
        split_ifs at ha with h1 h2
        · rw [Finset.mem_singleton] at ha; rw [ha]; exact h1.2
        · rw [Finset.mem_singleton] at ha; rw [ha]; exact h2.2
        · exact absurd ha (Finset.notMem_empty a)
      · rw [lbl_priv_or C n Si j hjw' hwP hop, Bool.or_eq_false_iff] at hlblw
        rw [stepFalse_or C n Si j hjw' hop, Finset.mem_filter, Finset.mem_insert,
          Finset.mem_singleton] at ha
        rcases ha.1 with rfl | rfl
        · have h1 := hlblw.1
          simp only [ha.2, ↓reduceIte] at h1
          exact h1
        · have h2 := hlblw.2
          simp only [ha.2, ↓reduceIte] at h2
          exact h2
    have hsupp_sub : supp C n (n + j) ⊆ (stepFalse C n Si (n + j)).biUnion (supp C n) := by
      rcases hgop with hop | hop
      · have hne : (supp C n (n + j)).Nonempty := Finset.card_pos.mp (by omega)
        obtain ⟨hu, hv, hsu, hsv⟩ := supp_and_children C hC j hjw' hop hne
        rw [lbl_priv_and C n Si j hjw' hwP hop] at hlblw
        simp only [hu, hv, ↓reduceIte, Bool.and_eq_false_iff] at hlblw
        rw [stepFalse_and C n Si j hjw' hop]
        intro p hp
        split_ifs with h1 h2
        · rw [Finset.singleton_biUnion]
          exact hsu hp
        · rw [Finset.singleton_biUnion]
          exact hsv hp
        · exfalso
          rcases hlblw with hl | hl
          · exact h1 ⟨hu, hl⟩
          · exact h2 ⟨hv, hl⟩
      · rw [stepFalse_or C n Si j hjw' hop]
        exact supp_or_biUnion C hC j hjw' hop
    refine ⟨?_, ?_⟩
    · intro a ha
      rcases Finset.mem_union.mp ha with ha1 | ha2
      · exact hGF.1 a (Finset.mem_erase.mp ha1).2
      · exact hstep_lbl a ha2
    · intro p hp
      have hpF := hGF.2 hp
      rw [Finset.mem_biUnion] at hpF ⊢
      obtain ⟨z, hzF, hpz⟩ := hpF
      by_cases hzw : z = n + j
      · subst hzw
        have hpS := hsupp_sub hpz
        rw [Finset.mem_biUnion] at hpS
        obtain ⟨a, haS, hpa⟩ := hpS
        exact ⟨a, Finset.mem_union_right _ haS, hpa⟩
      · exact ⟨z, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hzw, hzF⟩), hpz⟩
  obtain ⟨E, hE_out, hE_card, hGE⟩ := frontier_exit P Good (stepFalse C n Si)
    (fun w _ a ha => stepFalse_lt C n Si w a ha)
    (fun w _ => stepFalse_card C n Si w)
    hgood_step oi ⟨fun w hw => by rw [Finset.mem_singleton.mp hw]; exact hlbl,
      by simp⟩
  have he_card : ∀ e ∈ E, (supp C n e).card ≤ 1 := by
    intro e he
    have hnotP := hE_out e he
    have hlbl_e := hGE.1 e he
    rw [lbl_exit C n Si e hnotP] at hlbl_e
    have hsub : supp C n e ⊆ Si := by
      by_contra hnsub
      simp [hnsub] at hlbl_e
    by_contra hge2
    exact hnotP ((mem_privWires_iff C n Si e).mpr ⟨by omega, hsub⟩)
  have h1 : (supp C n oi).card ≤ (E.biUnion (supp C n)).card := Finset.card_le_card hGE.2
  have h2 : (E.biUnion (supp C n)).card ≤ ∑ e ∈ E, (supp C n e).card := Finset.card_biUnion_le
  have h3 : ∑ e ∈ E, (supp C n e).card ≤ ∑ _e ∈ E, 1 := Finset.sum_le_sum fun e he => he_card e he
  have h4 : ∑ _e ∈ E, 1 = E.card := by simp
  rw [privWires_card] at hE_card
  omega

theorem main :
    ∀ (n m k : ℕ) (S : Fin m → Finset (Fin n)) (C : Circuit) (o : Fin m → ℕ) (c : Fin m → ℕ),
      (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) →
      (∀ i : Fin m, 2 ≤ (Finset.univ.filter (fun a : Fin n => (C.wires (List.ofFn (fun b : Fin n => decide (b = a)))).getD (o i) false = true)).card) →
      (∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) →
      (∀ (i : Fin m) (p : Fin n), (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (o i) false = true → p ∈ S i) →
      (∀ (i : Fin m) (x : Fin n → Bool), (Finset.univ.filter (fun q : Fin n => x q = true)).card ≤ k → (∀ q ∈ S i, x q = false) → (C.wires (List.ofFn x)).getD (o i) false = false) →
      (∀ i : Fin m, c i ≤ k) →
      (∀ i : Fin m, c i + 1 ≤ (Finset.univ.filter (fun a : Fin n => (C.wires (List.ofFn (fun b : Fin n => decide (b = a)))).getD (o i) false = true)).card) →
      ∑ i : Fin m, c i ≤ C.size := by
  intro n m k S C o c hS_inter _hL_ge2 hC _hL_sub hprom hc_k hc_L
  have hbound : ∀ i : Fin m, c i ≤ (privGates C n (S i)).card := by
    intro i
    cases hlbl : lbl C n (S i) (o i)
    · exact case_false (S i) C (o i) (c i) hC (hc_L i) hlbl
    · exact case_true (S i) C (o i) (c i) hC (hprom i) (hc_k i) hlbl
  have hdisj : ∀ i ∈ (Finset.univ : Finset (Fin m)), ∀ j ∈ (Finset.univ : Finset (Fin m)),
      i ≠ j → Disjoint (privGates C n (S i)) (privGates C n (S j)) := by
    intro i _ j _ hij
    rw [Finset.disjoint_left]
    intro g hgi hgj
    rw [privGates, Finset.mem_filter] at hgi hgj
    have hsub : supp C n (n + g.val) ⊆ S i ∩ S j := Finset.subset_inter hgi.2.2 hgj.2.2
    have hc1 := Finset.card_le_card hsub
    have hc2 := hS_inter i j hij
    have hc3 := hgi.2.1
    omega
  calc ∑ i : Fin m, c i
      ≤ ∑ i : Fin m, (privGates C n (S i)).card := Finset.sum_le_sum fun i _ => hbound i
    _ = ((Finset.univ : Finset (Fin m)).biUnion (fun i => privGates C n (S i))).card :=
        (Finset.card_biUnion hdisj).symm
    _ ≤ (Finset.univ : Finset (Fin C.gates.length)).card :=
        Finset.card_le_card (Finset.subset_univ _)
    _ = C.size := by simp [Circuit.size]

end PEqualNP.Outside.L_meta_782

theorem PEqualNP.Outside.L_meta_782 : ∀ (n m k : ℕ) (S : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ) (c : Fin m → ℕ), (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ i : Fin m, 2 ≤ (Finset.univ.filter (fun a : Fin n => (C.wires (List.ofFn (fun b : Fin n => decide (b = a)))).getD (o i) false = true)).card) → (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) → (∀ (i : Fin m) (p : Fin n), (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (o i) false = true → p ∈ S i) → (∀ (i : Fin m) (x : Fin n → Bool), (Finset.univ.filter (fun q : Fin n => x q = true)).card ≤ k → (∀ q ∈ S i, x q = false) → (C.wires (List.ofFn x)).getD (o i) false = false) → (∀ i : Fin m, c i ≤ k) → (∀ i : Fin m, c i + 1 ≤ (Finset.univ.filter (fun a : Fin n => (C.wires (List.ofFn (fun b : Fin n => decide (b = a)))).getD (o i) false = true)).card) → ∑ i : Fin m, c i ≤ C.size := by
  exact PEqualNP.Outside.L_meta_782.main
