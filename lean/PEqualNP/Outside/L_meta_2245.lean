import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2245

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

-- The wires of a gate list, started from a given list of values.
def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

lemma wiresFrom_start (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

lemma length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_start gs w
  rw [ht]; simp [hl]

lemma getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_start gs w
  rw [ht, List.getD_append _ _ _ _ h]

lemma getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
    (L ++ [S]).getD k d = S := by
  subst h; simp

lemma split_at {α : Type} : ∀ (l : List α) (p : ℕ) (g : α), l[p]? = some g →
    ∃ pre post, l = pre ++ g :: post ∧ pre.length = p := by
  intro l
  induction l with
  | nil => intro p g h; simp at h
  | cons x l ih =>
    intro p g h
    cases p with
    | zero =>
      simp at h
      subst h
      exact ⟨[], l, rfl, rfl⟩
    | succ p =>
      simp at h
      obtain ⟨pre, post, rfl, rfl⟩ := ih p g h
      exact ⟨x :: pre, post, rfl, rfl⟩

lemma wire_at (n : ℕ) (pre post : List Gate) (g : Gate) (X : List Bool) (hX : X.length = n) :
    (wiresFrom (pre ++ g :: post) X).getD (n + pre.length) false
      = g.op.eval (g.inputs.map fun i => (wiresFrom pre X).getD i false) := by
  have h1 : wiresFrom (pre ++ g :: post) X = wiresFrom post
      (wiresFrom pre X ++ [g.op.eval (g.inputs.map fun i => (wiresFrom pre X).getD i false)]) := by
    rw [wiresFrom_append]; rfl
  have hl : (wiresFrom pre X).length = n + pre.length := by
    rw [length_wiresFrom]; omega
  rw [h1, getD_wiresFrom _ _ _ (by simp [hl]), getD_snoc_len _ _ _ _ hl]

-- The value of wire w.
def V (gs : List Gate) (x : List Bool) (w : ℕ) : Bool := (wiresFrom gs x).getD w false

lemma eval_eq (gs : List Gate) (out : ℕ) (x : List Bool) :
    Circuit.eval ⟨gs, out⟩ x = V gs x out := rfl

lemma V_start (pre post : List Gate) (x : List Bool) (w : ℕ) (h : w < x.length + pre.length) :
    V (pre ++ post) x w = V pre x w := by
  unfold V
  rw [wiresFrom_append, getD_wiresFrom _ _ _ (by rw [length_wiresFrom]; exact h)]

lemma gate_val (gs : List Gate) (x : List Bool) (hx : x.length = 26) (i : ℕ) (g : Gate)
    (hg : gs[i]? = some g) (hw : ∀ w ∈ g.inputs, w < 26 + i) :
    V gs x (26 + i) = g.op.eval (g.inputs.map (V gs x)) := by
  obtain ⟨pre, post, hsplit, hlen⟩ := split_at gs i g hg
  subst hsplit
  subst hlen
  have h1 : V (pre ++ g :: post) x (26 + pre.length)
      = g.op.eval (g.inputs.map fun w => (wiresFrom pre x).getD w false) :=
    wire_at 26 pre post g x hx
  rw [h1]
  congr 1
  apply List.map_congr_left
  intro w hwm
  exact (V_start pre (g :: post) x w (by rw [hx]; exact hw w hwm)).symm

lemma V_out (gs : List Gate) (x : List Bool) (w : ℕ) (h : x.length + gs.length ≤ w) :
    V gs x w = false := by
  unfold V
  exact List.getD_eq_default _ _ (by rw [length_wiresFrom]; exact h)

lemma V_in (gs gs' : List Gate) (x : List Bool) (w : ℕ) (h : w < x.length) :
    V gs x w = V gs' x w := by
  unfold V
  rw [getD_wiresFrom _ _ _ h, getD_wiresFrom _ _ _ h]

lemma gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k = C.gates[k] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]

-- Wire renaming after the deletion of gate j.
def sg (j : ℕ) (u : ℕ) : ℕ := if 26 + j < u then u - 1 else u

lemma sg_le (j u : ℕ) (h : u ≤ 26 + j) : sg j u = u := by
  have h' : ¬ 26 + j < u := by omega
  simp [sg, h']

lemma sg_gt (j u : ℕ) (h : 26 + j < u) : sg j u = u - 1 := by
  simp [sg, h]

def sh (j : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (sg j)⟩

-- Every reader of gate j reads the wire a in its place.
def f1 (j a : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (fun u => if u = 26 + j then a else u)⟩

def del (f : Gate → Gate) (j : ℕ) (gs : List Gate) : List Gate :=
  ((gs.map f).eraseIdx j).map (sh j)

lemma del_get (f : Gate → Gate) (j : ℕ) (gs : List Gate) (i : ℕ) (g : Gate)
    (hg : gs[i]? = some g) (hij : i ≠ j) :
    ∃ i', sg j (26 + i) = 26 + i' ∧ (del f j gs)[i']? = some (sh j (f g)) := by
  by_cases h : i < j
  · refine ⟨i, sg_le j _ (by omega), ?_⟩
    simp [del, List.getElem?_eraseIdx, h, hg]
  · obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
    have hk : ¬ k < j := by omega
    refine ⟨k, ?_, ?_⟩
    · rw [sg_gt j _ (by omega)]; omega
    · simp [del, List.getElem?_eraseIdx, hk, hg]

lemma del_inv (f : Gate → Gate) (j : ℕ) (gs : List Gate) (i' : ℕ) (g' : Gate)
    (h : (del f j gs)[i']? = some g') :
    ∃ i g, gs[i]? = some g ∧ g' = sh j (f g) ∧ ((i' = i ∧ i < j) ∨ (i' + 1 = i ∧ j ≤ i')) := by
  by_cases h3 : i' < j
  · simp [del, List.getElem?_eraseIdx, h3] at h
    obtain ⟨g, hg, rfl⟩ := h
    exact ⟨i', g, hg, rfl, Or.inl ⟨rfl, h3⟩⟩
  · simp [del, List.getElem?_eraseIdx, h3] at h
    obtain ⟨g, hg, rfl⟩ := h
    exact ⟨i' + 1, g, hg, rfl, Or.inr ⟨rfl, by omega⟩⟩

lemma del_back (f : Gate → Gate) (j : ℕ) (gs : List Gate)
    (hfb : ∀ (i : ℕ) (g : Gate), gs[i]? = some g → ∀ u ∈ (f g).inputs, u < 26 + i ∧ u ≠ 26 + j)
    (i' : ℕ) (g' : Gate) (h : (del f j gs)[i']? = some g') :
    ∀ u ∈ g'.inputs, u < 26 + i' := by
  obtain ⟨i, g, hg, rfl, hi⟩ := del_inv f j gs i' g' h
  intro u hu
  simp only [sh, List.mem_map] at hu
  obtain ⟨v, hv, rfl⟩ := hu
  have h1 := hfb i g hg v hv
  unfold sg
  split_ifs <;> omega

lemma f1_back (j a : ℕ) (gs : List Gate) (haj : a < 26 + j)
    (hback : ∀ (i : ℕ) (g : Gate), gs[i]? = some g → ∀ u ∈ g.inputs, u < 26 + i) :
    ∀ (i : ℕ) (g : Gate), gs[i]? = some g →
      ∀ u ∈ (f1 j a g).inputs, u < 26 + i ∧ u ≠ 26 + j := by
  intro i g hg u hu
  simp only [f1, List.mem_map] at hu
  obtain ⟨v, hv, rfl⟩ := hu
  have h1 := hback i g hg v hv
  split_ifs with h
  · subst h; exact ⟨by omega, by omega⟩
  · exact ⟨h1, h⟩

-- The comparison of the wires of the shorter list with the wires of the given one, for a
-- relation R on truth values that the two gate operations respect.
lemma del_rel (R : Bool → Bool → Prop) (hrefl : ∀ b, R b b)
    (htrans : ∀ p q r, R p q → R q r → R p r)
    (hop : ∀ (op : GateOp), op ∈ ({GateOp.and, GateOp.or} : Set GateOp) →
      ∀ (l : List ℕ) (F G : ℕ → Bool), (∀ u ∈ l, R (F u) (G u)) →
        R (op.eval (l.map F)) (op.eval (l.map G)))
    (j a : ℕ) (gs : List Gate) (hj : j < gs.length) (haj : a < 26 + j)
    (x : List Bool) (hx : x.length = 26)
    (hmono : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
    (hback : ∀ (i : ℕ) (g : Gate), gs[i]? = some g → ∀ u ∈ g.inputs, u < 26 + i)
    (hja : R (V gs x a) (V gs x (26 + j))) :
    ∀ u, u ≠ 26 + j → R (V (del (f1 j a) j gs) x (sg j u)) (V gs x u) := by
  have hfb := f1_back j a gs haj hback
  intro u
  induction u using Nat.strong_induction_on with
  | _ u ih =>
    intro hu
    have hlen : (del (f1 j a) j gs).length = gs.length - 1 := by
      simp [del, List.length_eraseIdx, hj]
    by_cases h1 : u < 26
    · rw [sg_le j u (by omega), V_in _ gs x u (by omega)]
      exact hrefl _
    · obtain ⟨i, rfl⟩ : ∃ i, u = 26 + i := ⟨u - 26, by omega⟩
      have hij : i ≠ j := by omega
      by_cases h2 : i < gs.length
      · have hg : gs[i]? = some gs[i] := List.getElem?_eq_getElem h2
        obtain ⟨i', hs, hd⟩ := del_get (f1 j a) j gs i gs[i] hg hij
        rw [hs, gate_val _ x hx i' _ hd (del_back (f1 j a) j gs hfb i' _ hd),
          gate_val gs x hx i _ hg (hback i _ hg)]
        have hin : (sh j (f1 j a gs[i])).inputs.map (V (del (f1 j a) j gs) x)
            = gs[i].inputs.map
              (fun w => V (del (f1 j a) j gs) x (sg j (if w = 26 + j then a else w))) := by
          simp [sh, f1, List.map_map, Function.comp_def]
        have hopeq : (sh j (f1 j a gs[i])).op = gs[i].op := rfl
        rw [hin, hopeq]
        apply hop _ (hmono _ (List.getElem_mem h2))
        intro w hw
        have hwi := hback i _ hg w hw
        by_cases hwj : w = 26 + j
        · subst hwj
          have hif : (if 26 + j = 26 + j then a else 26 + j) = a := by simp
          rw [hif]
          exact htrans _ _ _ (ih a (by omega) (by omega)) hja
        · have hif : (if w = 26 + j then a else w) = w := by simp [hwj]
          rw [hif]
          exact ih w hwi hwj
      · rw [V_out gs x _ (by omega),
          V_out _ x _ (by rw [hlen]; unfold sg; split_ifs <;> omega)]
        exact hrefl _

lemma hop_eq : ∀ (op : GateOp), op ∈ ({GateOp.and, GateOp.or} : Set GateOp) →
    ∀ (l : List ℕ) (F G : ℕ → Bool), (∀ u ∈ l, F u = G u) →
      op.eval (l.map F) = op.eval (l.map G) := by
  intro op _ l F G h
  rw [List.map_congr_left h]

-- R p q says that q true gives p true.
lemma hop_ge : ∀ (op : GateOp), op ∈ ({GateOp.and, GateOp.or} : Set GateOp) →
    ∀ (l : List ℕ) (F G : ℕ → Bool), (∀ u ∈ l, G u = true → F u = true) →
      (op.eval (l.map G) = true → op.eval (l.map F) = true) := by
  intro op hop l F G h
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true, List.mem_map, id]
    rintro H b ⟨u, hu, rfl⟩
    exact h u hu (H _ ⟨u, hu, rfl⟩)
  · simp only [GateOp.eval, List.any_eq_true, List.mem_map, id]
    rintro ⟨b, ⟨u, hu, rfl⟩, hb⟩
    exact ⟨_, ⟨u, hu, rfl⟩, h u hu hb⟩

-- The values of gate j and of one of its inputs.
lemma and_le (l : List ℕ) (F : ℕ → Bool) (a : ℕ) (ha : a ∈ l)
    (h : GateOp.and.eval (l.map F) = true) : F a = true := by
  simp only [GateOp.eval, List.all_eq_true, List.mem_map, id] at h
  exact h _ ⟨a, ha, rfl⟩

lemma le_or (l : List ℕ) (F : ℕ → Bool) (a : ℕ) (ha : a ∈ l)
    (h : F a = true) : GateOp.or.eval (l.map F) = true := by
  simp only [GateOp.eval, List.any_eq_true, List.mem_map, id]
  exact ⟨_, ⟨a, ha, rfl⟩, h⟩

theorem bridge (C : Circuit) (rows : Bool → List Bool → Prop)
    (hrows : ∀ s x, rows s x → x.length = 26)
    (hC1 : Monotone2 C) (hC2 : ReadsBack 26 C) (hC3 : ∀ s x, rows s x → C.eval x = s)
    (hne : ¬ (∀ j < C.gates.length, ∀ a ∈ (gateAt C j).inputs,
      ∃ x, rows (!(gateAt C j).op.eval []) x ∧
        (C.wires x).getD a false = !(!(gateAt C j).op.eval []) ∧
        (C.wires x).getD (26 + j) false = !(gateAt C j).op.eval [])) :
    ∃ D : Circuit, (Monotone2 D ∧ ReadsBack 26 D ∧ ∀ s x, rows s x → D.eval x = s) ∧
      D.size < C.size := by
  obtain ⟨gs, out⟩ := C
  push Not at hne
  obtain ⟨j, hj, a, ha, hall⟩ := hne
  change j < gs.length at hj
  have hgj : gateAt ⟨gs, out⟩ j = gs[j] := gateAt_eq _ j hj
  rw [hgj] at ha hall
  have hall' : ∀ x : List Bool, rows (!gs[j].op.eval []) x →
      V gs x a = !(!gs[j].op.eval []) → V gs x (26 + j) ≠ !gs[j].op.eval [] := hall
  have hmono : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) := fun g hg => (hC1 g hg).1
  have hback : ∀ (i : ℕ) (g : Gate), gs[i]? = some g → ∀ u ∈ g.inputs, u < 26 + i := by
    intro i g hg u hu
    obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.1 hg
    have := hC2 i hi u (by rw [gateAt_eq _ i hi]; exact hu)
    exact this
  have hgj' : gs[j]? = some gs[j] := List.getElem?_eq_getElem hj
  have haj : a < 26 + j := hback j _ hgj' a ha
  have hval : ∀ x : List Bool, x.length = 26 →
      V gs x (26 + j) = gs[j].op.eval (gs[j].inputs.map (V gs x)) :=
    fun x hx => gate_val gs x hx j _ hgj' (hback j _ hgj')
  have hfb := f1_back j a gs haj hback
  have hout' : (if out = 26 + j then a else out) ≠ 26 + j := by
    split_ifs with h
    · omega
    · exact h
  refine ⟨⟨del (f1 j a) j gs, sg j (if out = 26 + j then a else out)⟩, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro g' hg'
    obtain ⟨i', hi'⟩ := List.getElem?_of_mem hg'
    obtain ⟨i, g, hg, rfl, _⟩ := del_inv (f1 j a) j gs i' g' hi'
    have h := hC1 g (List.mem_of_getElem? hg)
    exact ⟨h.1, by simpa [sh, f1] using h.2⟩
  · intro i' hi' u hu
    rw [gateAt_eq _ i' hi'] at hu
    exact del_back (f1 j a) j gs hfb i' _ (List.getElem?_eq_getElem hi') u hu
  · intro s x hr
    have hx := hrows s x hr
    have hCx : V gs x out = s := hC3 s x hr
    change V (del (f1 j a) j gs) x (sg j (if out = 26 + j then a else out)) = s
    have hv := hval x hx
    rcases hmono _ (List.getElem_mem hj) with hop | hop
    · -- gate j is an AND gate: its value is below the value of the wire a
      have hle : V gs x (26 + j) = true → V gs x a = true := by
        intro h
        rw [hv, hop] at h
        exact and_le _ _ a ha h
      cases s with
      | true =>
        have hrel := del_rel (fun p q => q = true → p = true) (fun _ h => h)
          (fun _ _ _ h1 h2 h => h1 (h2 h)) hop_ge j a gs hj haj x hx hmono hback hle
          _ hout'
        apply hrel
        split_ifs with h
        · subst h; exact hle hCx
        · exact hCx
      | false =>
        have hs : (!gs[j].op.eval []) = false := by rw [hop]; rfl
        have hge : V gs x a = true → V gs x (26 + j) = true := by
          intro h
          have h2 := hall' x (by rw [hs]; exact hr) (by rw [hs]; exact h)
          rw [hs] at h2
          simpa using h2
        have heq : V gs x a = V gs x (26 + j) := by
          rw [Bool.eq_iff_iff]; exact ⟨hge, hle⟩
        have hrel := del_rel Eq (fun _ => rfl) (fun _ _ _ h1 h2 => h1.trans h2) hop_eq
          j a gs hj haj x hx hmono hback heq _ hout'
        rw [hrel]
        split_ifs with h
        · subst h; rw [heq]; exact hCx
        · exact hCx
    · -- gate j is an OR gate: its value is above the value of the wire a
      have hle : V gs x a = true → V gs x (26 + j) = true := by
        intro h
        rw [hv, hop]
        exact le_or _ _ a ha h
      cases s with
      | true =>
        have hge : V gs x (26 + j) = true → V gs x a = true := by
          intro h
          by_contra hna
          have hs : (!gs[j].op.eval []) = true := by rw [hop]; rfl
          have hna' : V gs x a = false := by simpa using hna
          have h2 := hall' x (by rw [hs]; exact hr) (by rw [hs]; exact hna')
          rw [hs] at h2
          exact h2 h
        have heq : V gs x a = V gs x (26 + j) := by
          rw [Bool.eq_iff_iff]; exact ⟨hle, hge⟩
        have hrel := del_rel Eq (fun _ => rfl) (fun _ _ _ h1 h2 => h1.trans h2) hop_eq
          j a gs hj haj x hx hmono hback heq _ hout'
        rw [hrel]
        split_ifs with h
        · subst h; rw [heq]; exact hCx
        · exact hCx
      | false =>
        have hrel := del_rel (fun p q => p = true → q = true) (fun _ h => h)
          (fun _ _ _ h1 h2 h => h2 (h1 h))
          (fun op hop l F G h => hop_ge op hop l G F h) j a gs hj haj x hx hmono hback hle
          _ hout'
        rw [← Bool.not_eq_true]
        intro hD
        have h3 := hrel hD
        have h4 : V gs x out = true := by
          split_ifs at h3 with h
          · subst h; exact hle h3
          · exact h3
        rw [hCx] at h4
        exact Bool.false_ne_true h4
  · show (del (f1 j a) j gs).length < gs.length
    have hlen : (del (f1 j a) j gs).length = gs.length - 1 := by
      simp [del, List.length_eraseIdx, hj]
    rw [hlen]
    omega

end PEqualNP.Outside.L_meta_2245

theorem PEqualNP.Outside.L_meta_2245 : have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : Bool → List Bool → Prop := fun (x2 : Bool) (x3 : List Bool) => if x2 = Bool.true then ∃ (x4 : Fin (13 : ℕ)) (x5 : Fin (13 : ℕ)), x4 - x5 ∈ x1 ∧ x3 = (List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x4)) ++ List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x5) else ∃ (x4 : Finset (Fin (13 : ℕ))), x4.card = (4 : ℕ) ∧ (∀ (x5 : Fin (13 : ℕ)), {x6 ∈ x4 | x6 - x5 ∈ x1}.card ≤ (2 : ℕ)) ∧ x3 = (List.ofFn fun (x5 : Fin (13 : ℕ)) => Decidable.decide (x5 ∈ x4)) ++ List.ofFn fun (x5 : Fin (13 : ℕ)) => Decidable.decide (∀ x6 ∈ x4, x6 - x5 ∉ x1); have x3 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) => PEqualNP.MetaComplexity.Monotone2 x3 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x3 ∧ ∀ (x4 : Bool) (x5 : List Bool), x2 x4 x5 → x3.eval x5 = x4; have x4 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x4 : PEqualNP.CircuitLowerBounds.Circuit) => ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit), x3 x5 ∧ x5.size < x4.size; have x5 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x5 : PEqualNP.CircuitLowerBounds.Circuit) =>   ∀ x6 < x5.gates.length,     have x8 : PEqualNP.CircuitLowerBounds.Gate := PEqualNP.MetaComplexity.NestedCover.gateAt x5 x6;     have x9 : Bool := !x8.op.eval [];     ∀ x10 ∈ x8.inputs, ∃ (x12 : List Bool), x2 x9 x12 ∧ (x5.wires x12).getD x10 Bool.false = !x9 ∧ (x5.wires x12).getD ((26 : ℕ) + x6) Bool.false = x9; ∀ (x6 : PEqualNP.CircuitLowerBounds.Circuit), x3 x6 → x4 x6 ∨ x5 x6 := by
  intro x1 x2 x3 x4 x5 C hC
  by_cases h : x5 C
  · exact Or.inr h
  · refine Or.inl (PEqualNP.Outside.L_meta_2245.bridge C x2 ?_ hC.1 hC.2.1 hC.2.2 h)
    intro s x hr
    cases s with
    | true =>
      obtain ⟨p, l, _, rfl⟩ := hr
      simp
    | false =>
      obtain ⟨Q, _, _, rfl⟩ := hr
      simp
