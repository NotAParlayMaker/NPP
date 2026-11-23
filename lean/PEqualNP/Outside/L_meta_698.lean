import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_698

open PEqualNP.MetaComplexity

def step (w : List Bool) (G : BinaryGate) : List Bool :=
  w ++ [G.op (w.getD G.left false) (w.getD G.right false)]

lemma fold_length (gs : List BinaryGate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons G gs ih => simp [List.foldl_cons, ih, step]; omega

lemma fold_get (gs : List BinaryGate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons G gs ih =>
    rw [List.foldl_cons, ih _ (by simp [step]; omega)]
    simp [step, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

def val {n : ℕ} (D : BinaryCircuit) (x : Fin n → Bool) (i : ℕ) : Bool :=
  (D.wires (List.ofFn x)).getD i false

lemma val_input {n : ℕ} (D : BinaryCircuit) (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
    val D x i = x ⟨i, hi⟩ := by
  unfold val BinaryCircuit.wires
  change (D.gates.foldl step (List.ofFn x)).getD i false = _
  rw [fold_get _ _ _ (by simpa using hi)]
  simp [List.getD_eq_getElem?_getD, hi]

lemma val_large {n : ℕ} (D : BinaryCircuit) (x : Fin n → Bool) (i : ℕ)
    (hi : n + D.gates.length ≤ i) : val D x i = false := by
  have hlen : (D.wires (List.ofFn x)).length = n + D.gates.length := by
    change (D.gates.foldl step (List.ofFn x)).length = _
    simp [fold_length]
  simp [val, List.getD_eq_getElem?_getD, List.getElem?_eq_none (hlen ▸ hi)]

lemma val_gate {n : ℕ} (D : BinaryCircuit) (x : Fin n → Bool) (j : ℕ) (G : BinaryGate)
    (hG : D.gates[j]? = some G) :
    val D x (n + j) =
      G.op (if G.left < n + j then val D x G.left else false)
        (if G.right < n + j then val D x G.right else false) := by
  obtain ⟨hj, rfl⟩ := List.getElem?_eq_some_iff.mp hG
  let w := (D.gates.take j).foldl step (List.ofFn x)
  have hlen : w.length = n + j := by simp [w, fold_length, Nat.min_eq_left hj.le]
  have hsplit : D.gates = D.gates.take j ++ D.gates[j] :: D.gates.drop (j + 1) := by
    simp [List.take_append_drop]
  have hall : D.wires (List.ofFn x) =
      (D.gates.drop (j + 1)).foldl step (step w D.gates[j]) := by
    change D.gates.foldl step (List.ofFn x) = _
    conv_lhs => rw [hsplit, List.foldl_append, List.foldl_cons]
  have hread (i : ℕ) : w.getD i false = if i < n + j then val D x i else false := by
    by_cases hi : i < n + j
    · simp only [hi, if_pos]
      symm
      change (D.wires (List.ofFn x)).getD i false = w.getD i false
      rw [hall, fold_get _ _ _ (by simp only [step, List.length_append, List.length_singleton]; omega)]
      simp only [step, List.getD_eq_getElem?_getD,
        List.getElem?_append_left (show i < w.length by omega)]
    · simp [hi, List.getD_eq_getElem?_getD, List.getElem?_eq_none (show w.length ≤ i by omega)]
  calc
    val D x (n + j) = D.gates[j].op (w.getD D.gates[j].left false)
        (w.getD D.gates[j].right false) := by
      change (D.wires (List.ofFn x)).getD (n + j) false = _
      rw [hall, fold_get _ _ _ (by simp [step, hlen])]
      change (w ++ [_]).getD (n + j) false = _
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
      simp only [hlen, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
    _ = _ := by rw [hread, hread]

lemma agree {n : ℕ} (D : BinaryCircuit) (x y : Fin n → Bool) (v u : Fin n)
    (g h k limit : ℕ)
    (hxy : ∀ z, z ≠ v → z ≠ u → x z = y z)
    (rv : ∀ j G, D.gates[j]? = some G → (G.left = v.val ∨ G.right = v.val) → j = g)
    (ru : ∀ j G, D.gates[j]? = some G → (G.left = u.val ∨ G.right = u.val) → j = h)
    (rg : ∀ j G, D.gates[j]? = some G → (G.left = n + g ∨ G.right = n + g) → g < j → j = k)
    (rh : ∀ j G, D.gates[j]? = some G → (G.left = n + h ∨ G.right = n + h) → h < j → j = k)
    (hk : n + k < limit → val D x (n + k) = val D y (n + k)) :
    ∀ w, w < limit → w ≠ v.val → w ≠ u.val → w ≠ n + g → w ≠ n + h →
      val D x w = val D y w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw hv hu hg hh
    by_cases hn : w < n
    · rw [val_input D x w hn, val_input D y w hn]
      apply hxy
      · intro e; exact hv (congrArg Fin.val e)
      · intro e; exact hu (congrArg Fin.val e)
    · by_cases hlarge : n + D.gates.length ≤ w
      · rw [val_large D x w hlarge, val_large D y w hlarge]
      · let j := w - n
        have hwj : w = n + j := by omega
        have hj : j < D.gates.length := by omega
        let G := D.gates[j]
        have hG : D.gates[j]? = some G := List.getElem?_eq_getElem hj
        by_cases hjk : j = k
        · rw [hwj, hjk]
          exact hk (by omega)
        · have hr (t : ℕ) (htread : G.left = t ∨ G.right = t) :
              (if t < n + j then val D x t else false) =
                (if t < n + j then val D y t else false) := by
            split_ifs with ht
            · apply ih t (by omega) (by omega)
              · intro e
                have := rv j G hG (e ▸ htread)
                omega
              · intro e
                have := ru j G hG (e ▸ htread)
                omega
              · intro e
                have := rg j G hG (e ▸ htread) (by omega)
                exact hjk this
              · intro e
                have := rh j G hG (e ▸ htread) (by omega)
                exact hjk this
            · rfl
          rw [hwj, val_gate D x j G hG, val_gate D y j G hG]
          rw [hr G.left (Or.inl rfl), hr G.right (Or.inr rfl)]

end PEqualNP.Outside.L_meta_698

theorem PEqualNP.Outside.L_meta_698 : ∀ (n : ℕ) (D : PEqualNP.MetaComplexity.BinaryCircuit) (v u : Fin n) (g h k : ℕ), v ≠ u → g ≠ h → (∀ j : ℕ, (∃ G : PEqualNP.MetaComplexity.BinaryGate, D.gates[j]? = some G ∧ (G.left = v.val ∨ G.right = v.val)) ↔ j = g) → (∀ j : ℕ, (∃ G : PEqualNP.MetaComplexity.BinaryGate, D.gates[j]? = some G ∧ (G.left = u.val ∨ G.right = u.val)) ↔ j = h) → (∃ G : PEqualNP.MetaComplexity.BinaryGate, D.gates[g]? = some G ∧ ¬ (G.left = v.val ∧ G.right = v.val)) → (∃ G : PEqualNP.MetaComplexity.BinaryGate, D.gates[h]? = some G ∧ ¬ (G.left = u.val ∧ G.right = u.val)) → (∀ j : ℕ, (∃ G : PEqualNP.MetaComplexity.BinaryGate, D.gates[j]? = some G ∧ (G.left = n + g ∨ G.right = n + g) ∧ g < j) ↔ j = k) → (∀ j : ℕ, (∃ G : PEqualNP.MetaComplexity.BinaryGate, D.gates[j]? = some G ∧ (G.left = n + h ∨ G.right = n + h) ∧ h < j) ↔ j = k) → (∃ G : PEqualNP.MetaComplexity.BinaryGate, D.gates[k]? = some G ∧ ((G.op false false = false ∧ G.op false true = true ∧ G.op true false = true ∧ G.op true true = false) ∨ (G.op false false = true ∧ G.op false true = false ∧ G.op true false = false ∧ G.op true true = true))) → D.output ≠ v.val → D.output ≠ u.val → D.output ≠ n + g → D.output ≠ n + h → ∀ (x : Fin n → Bool) (f : Bool → Bool → Bool), (∀ a b : Bool, f a b = D.eval (List.ofFn (Function.update (Function.update x v a) u b))) → (f false false = f true true ∨ (∀ a b : Bool, f a b = f (!a) b) ∨ (∀ a b : Bool, f a b = f a (!b))) := by
  classical
  intro n D v u g h k hvu hgh hrv hru _ _ hrg hrh hkop hov hou hog hoh x f hf
  let y (a b : Bool) := Function.update (Function.update x v a) u b
  have rv j G hG hr := (hrv j).mp ⟨G, hG, hr⟩
  have ru j G hG hr := (hru j).mp ⟨G, hG, hr⟩
  have rg j G hG hr hlt := (hrg j).mp ⟨G, hG, hr, hlt⟩
  have rh j G hG hr hlt := (hrh j).mp ⟨G, hG, hr, hlt⟩
  obtain ⟨K, hK, hop⟩ := hkop
  obtain ⟨K₁, hK₁, hleft, hgk⟩ := (hrg k).mpr rfl
  obtain ⟨K₂, hK₂, hright, hhk⟩ := (hrh k).mpr rfl
  have e₁ : K₁ = K := Option.some.inj (hK₁.symm.trans hK)
  have e₂ : K₂ = K := Option.some.inj (hK₂.symm.trans hK)
  subst K₁
  subst K₂
  have hshape : (K.left = n + g ∧ K.right = n + h) ∨
      (K.left = n + h ∧ K.right = n + g) := by omega
  let α a := PEqualNP.Outside.L_meta_698.val D (y a false) (n + g)
  let β b := PEqualNP.Outside.L_meta_698.val D (y false b) (n + h)
  have ha (a b : Bool) : PEqualNP.Outside.L_meta_698.val D (y a b) (n + g) = α a := by
    apply PEqualNP.Outside.L_meta_698.agree D (y a b) (y a false) u u h h k (n + k)
      (fun z hz _ => by simp [y, hz]) ru ru rh rh (fun hh => False.elim (by omega))
    all_goals omega
  have hb (a b : Bool) : PEqualNP.Outside.L_meta_698.val D (y a b) (n + h) = β b := by
    apply PEqualNP.Outside.L_meta_698.agree D (y a b) (y false b) v v g g k (n + k)
      (fun z hz _ => by simp [y, Function.update_apply, hz]) rv rv rg rg
      (fun hh => False.elim (by omega))
    all_goals omega
  have comm (a b : Bool) : K.op a b = K.op b a := by
    rcases hop with ⟨h00, h01, h10, h11⟩ | ⟨h00, h01, h10, h11⟩ <;>
      cases a <;> cases b <;> simp only [h00, h01, h10, h11]
  let q (a b : Bool) := K.op (α a) (β b)
  have hkval (a b : Bool) : PEqualNP.Outside.L_meta_698.val D (y a b) (n + k) = q a b := by
    rw [PEqualNP.Outside.L_meta_698.val_gate D (y a b) k K hK]
    rcases hshape with ⟨hl, hr⟩ | ⟨hl, hr⟩
    · simp only [hl, hr, Nat.add_lt_add_iff_left, hgk, hhk, if_pos, ha, hb]
      rfl
    · simp only [hl, hr, Nat.add_lt_add_iff_left, hgk, hhk, if_pos, ha, hb]
      exact comm _ _
  have same (a b c d : Bool) (heq : q a b = q c d) : f a b = f c d := by
    rw [hf a b, hf c d]
    change PEqualNP.Outside.L_meta_698.val D (y a b) D.output =
      PEqualNP.Outside.L_meta_698.val D (y c d) D.output
    exact PEqualNP.Outside.L_meta_698.agree D (y a b) (y c d) v u g h k (D.output + 1)
      (fun z hzv hzu => by simp [y, hzv, hzu]) rv ru rg rh
      (fun _ => (hkval a b).trans (heq.trans (hkval c d).symm))
      D.output (by omega) hov hou hog hoh
  by_cases hα : α false = α true
  · right; left
    intro a b
    apply same
    cases a <;> simp [q, hα]
  · by_cases hβ : β false = β true
    · right; right
      intro a b
      apply same
      cases b <;> simp [q, hβ]
    · left
      apply same
      dsimp [q]
      rcases hop with ⟨h00, h01, h10, h11⟩ | ⟨h00, h01, h10, h11⟩ <;>
        cases h0 : α false <;> cases h1 : α true <;>
        cases h2 : β false <;> cases h3 : β true <;>
        simp only [h0, h1, Bool.false_eq_true, Bool.true_eq_false, not_true_eq_false] at hα <;>
        simp only [h2, h3, Bool.false_eq_true, Bool.true_eq_false, not_true_eq_false] at hβ <;>
        simp only [h0, h1, h2, h3, h00, h01, h10, h11]
