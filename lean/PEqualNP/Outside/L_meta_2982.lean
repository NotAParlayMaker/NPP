import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2982
open PEqualNP.CircuitLowerBounds

section
open PEqualNP.MetaComplexity
def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_start (gs : List Gate) : ∀ w : List Bool,
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

theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_start gs w
  rw [ht]; simp [hl]

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_start gs w
  rw [ht, List.getD_append _ _ _ _ h]

def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

variable {n : ℕ}

theorem dsn_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem dsn_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

def gateSupp (L : List (Finset (Fin n))) (g : Gate) : Finset (Fin n) :=
  (g.inputs.map fun a => L.getD a ∅).foldr (· ∪ ·) ∅

theorem mem_foldr_union (l : List ℕ) (F : ℕ → Finset (Fin n)) (i : Fin n) :
    i ∈ (l.map F).foldr (· ∪ ·) ∅ ↔ ∃ a ∈ l, i ∈ F a := by
  induction l with
  | nil => simp
  | cons b l ih => simp [ih]

theorem mem_gateSupp (L : List (Finset (Fin n))) (g : Gate) (i : Fin n) :
    i ∈ gateSupp L g ↔ ∃ a ∈ g.inputs, i ∈ L.getD a ∅ :=
  mem_foldr_union _ _ _

def suppsFrom (gs : List Gate) (L : List (Finset (Fin n))) : List (Finset (Fin n)) :=
  gs.foldl (fun L g => L ++ [gateSupp L g]) L

def inputSupps (n : ℕ) : List (Finset (Fin n)) := List.ofFn fun i : Fin n => {i}

def Agree (x y : Fin n → Bool) (L : List (Finset (Fin n))) (w w' : List Bool) : Prop :=
  L.length = w.length ∧ w.length = w'.length ∧
    ∀ j : ℕ, (∀ i ∈ L.getD j ∅, x i = y i) → w.getD j false = w'.getD j false

theorem agree_wiresFrom (x y : Fin n → Bool) (gs : List Gate) :
    ∀ (L : List (Finset (Fin n))) (w w' : List Bool), Agree x y L w w' →
      Agree x y (suppsFrom gs L) (wiresFrom gs w) (wiresFrom gs w') := by
  induction gs with
  | nil => intro L w w' h; exact h
  | cons g gs ih =>
    intro L w w' h
    obtain ⟨h1, h2, h3⟩ := h
    apply ih (L ++ [gateSupp L g])
      (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)])
    refine ⟨by simp [h1], by simp [h2], ?_⟩
    intro j hj
    by_cases hjl : j = L.length
    · subst hjl
      rw [dsn_eq] at hj
      rw [h1, dsn_eq, h2, dsn_eq]
      congr 1
      apply List.map_congr_left
      intro a ha
      exact h3 a (fun i hi => hj i ((mem_gateSupp L g i).2 ⟨a, ha, hi⟩))
    · rw [dsn_ne _ _ _ _ hjl] at hj
      rw [dsn_ne _ _ _ _ (by omega), dsn_ne _ _ _ _ (by omega)]
      exact h3 j hj

theorem agree_inputs (x y : Fin n → Bool) :
    Agree x y (inputSupps n) (List.ofFn x) (List.ofFn y) := by
  refine ⟨by simp [inputSupps], by simp, ?_⟩
  intro j hj
  by_cases hjn : j < n
  · have hx : x ⟨j, hjn⟩ = y ⟨j, hjn⟩ := hj _ (by simp [inputSupps, hjn])
    simp [hjn, hx]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

def Cnt (t : ℕ) (L : List (Finset (Fin n))) : Prop :=
  ∀ W : Finset ℕ, (W.biUnion fun j => L.getD j ∅).card ≤ t + W.card

theorem cnt_inputs : Cnt 0 (inputSupps n) := by
  intro W
  refine le_trans Finset.card_biUnion_le ?_
  rw [zero_add, Finset.card_eq_sum_ones]
  apply Finset.sum_le_sum
  intro j _
  by_cases hjn : j < n
  · simp [inputSupps, hjn]
  · rw [List.getD_eq_default _ _ (by simp [inputSupps]; omega)]; simp

theorem cnt_step (t : ℕ) (L : List (Finset (Fin n))) (g : Gate) (hg : g.inputs.length ≤ 2)
    (h : Cnt t L) : Cnt (t + 1) (L ++ [gateSupp L g]) := by
  intro W
  by_cases hW : L.length ∈ W
  · have hsub : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
        ⊆ ((W.erase L.length ∪ g.inputs.toFinset).biUnion fun j => L.getD j ∅) := by
      intro i hi
      rw [Finset.mem_biUnion] at hi ⊢
      obtain ⟨j, hjW, hij⟩ := hi
      by_cases hjl : j = L.length
      · subst hjl
        rw [dsn_eq] at hij
        obtain ⟨a, ha, hia⟩ := (mem_gateSupp L g i).1 hij
        exact ⟨a, Finset.mem_union_right _ (List.mem_toFinset.2 ha), hia⟩
      · rw [dsn_ne _ _ _ _ hjl] at hij
        exact ⟨j, Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hjl, hjW⟩), hij⟩
    have hc1 : (W.erase L.length ∪ g.inputs.toFinset).card ≤ (W.card - 1) + 2 := by
      refine le_trans (Finset.card_union_le _ _) ?_
      rw [Finset.card_erase_of_mem hW]
      exact Nat.add_le_add_left (le_trans (List.toFinset_card_le _) hg) _
    have hWpos : 1 ≤ W.card := Finset.card_pos.2 ⟨_, hW⟩
    have := h (W.erase L.length ∪ g.inputs.toFinset)
    have := Finset.card_le_card hsub
    omega
  · have heq : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
        = (W.biUnion fun j => L.getD j ∅) := by
      apply Finset.biUnion_congr rfl
      intro j hj
      exact dsn_ne _ _ _ _ (fun e => hW (e ▸ hj))
    rw [heq]
    have := h W
    omega

theorem cnt_suppsFrom (gs : List Gate) : ∀ (t : ℕ) (L : List (Finset (Fin n))),
    (∀ g ∈ gs, Ok g) → Cnt t L → Cnt (t + gs.length) (suppsFrom gs L) := by
  induction gs with
  | nil => intro t L _ h; exact h
  | cons g gs ih =>
    intro t L hok h
    have := ih (t + 1) (L ++ [gateSupp L g]) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      (cnt_step t L g (hok g List.mem_cons_self).2 h)
    rw [List.length_cons, show t + (gs.length + 1) = t + 1 + gs.length by omega]
    exact this

theorem dep_lower (n : ℕ) (f : (Fin n → Bool) → Bool)
    (hdep : ∀ i : Fin n, ∃ x : Fin n → Bool, f (Function.update x i (!x i)) ≠ f x)
    (s : ℕ) (h : HasCircuitSize n f s) : n ≤ s + 1 := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  set S := (suppsFrom C.gates (inputSupps n)).getD C.output ∅ with hS
  have hall : ∀ i : Fin n, i ∈ S := by
    intro i
    by_contra hi
    obtain ⟨x, hx⟩ := hdep i
    apply hx
    have hag := (agree_wiresFrom (Function.update x i (!x i)) x C.gates _ _ _
      (agree_inputs _ _)).2.2 C.output (by
        intro k hk
        have : k ≠ i := fun e => hi (e ▸ hk)
        simp [Function.update_of_ne this])
    rw [← hev, ← hev]
    exact hag
  have hcard : S.card = n := by
    rw [Finset.eq_univ_of_forall hall]; simp
  have hc := cnt_suppsFrom C.gates 0 (inputSupps n) ok cnt_inputs {C.output}
  simp only [Finset.singleton_biUnion, Finset.card_singleton, zero_add] at hc
  rw [← hS, hcard] at hc
  omega
end

end PEqualNP.Outside.L_meta_2982

open PEqualNP.Outside.L_meta_2982 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_2982 : ∀ (x1 : ℕ) (x2 : Fin x1 → Finset (Fin x1)) (x3 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x4 : Fin x1), (x2 x4).Nonempty) → (∀ (x5 : Fin x1), ∃ (x6 : Fin x1), x5 ∈ x2 x6) → PEqualNP.TopForm.IsAO2 (x1 + x1) x3 → PEqualNP.GenericRejection.RightOnIncidentPairs x2 x3 → (∀ (x8 x9 : Finset (Fin x1)), x8.card + x9.card = (1 : ℕ) → x3.eval (PEqualNP.GenericRejection.incidenceInput x8 x9) = Bool.false) → x1 + x1 ≤ x3.size + (1 : ℕ) := by
  intro n S C hne0 hcov hC hright hfalse
  have hne : ∀ a b : Fin n, Fin.castAdd n a ≠ Fin.natAdd n b := by
    intro a b h
    have := congrArg Fin.val h
    simp at this
    omega
  have hinjc : ∀ a b : Fin n, Fin.castAdd n a = Fin.castAdd n b → a = b := by
    intro a b h
    have := congrArg Fin.val h
    simp at this
    exact Fin.ext this
  have hinjn : ∀ a b : Fin n, Fin.natAdd n a = Fin.natAdd n b → a = b := by
    intro a b h
    have := congrArg Fin.val h
    simp at this
    exact Fin.ext this
  have hsize : PEqualNP.MetaComplexity.HasCircuitSize (n + n)
      (fun x : Fin (n + n) → Bool => C.eval (List.ofFn x)) C.size := by
    refine ⟨C, ?_, le_refl _, fun x => rfl⟩
    intro g hg
    refine ⟨?_, le_of_eq (hC.2.2 g hg)⟩
    rcases hC.1 g hg with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  have E : ∀ X Y : Finset (Fin n), List.ofFn (Fin.append (fun p' : Fin n => decide (p' ∈ X))
      (fun l' : Fin n => decide (l' ∈ Y))) = PEqualNP.GenericRejection.incidenceInput X Y :=
    fun X Y => List.ofFn_fin_append _ _
  have hdep : ∀ i : Fin (n + n), ∃ x : Fin (n + n) → Bool,
      (fun x : Fin (n + n) → Bool => C.eval (List.ofFn x)) (Function.update x i (!x i))
        ≠ (fun x : Fin (n + n) → Bool => C.eval (List.ofFn x)) x := by
    intro i
    refine Fin.addCases (fun p => ?_) (fun l => ?_) i
    · obtain ⟨l, hp⟩ := hcov p
      refine ⟨Fin.append (fun p' : Fin n => decide (p' ∈ ({p} : Finset (Fin n))))
        (fun l' : Fin n => decide (l' ∈ ({l} : Finset (Fin n)))), ?_⟩
      have U : Function.update (Fin.append (fun p' : Fin n => decide (p' ∈ ({p} : Finset (Fin n))))
            (fun l' : Fin n => decide (l' ∈ ({l} : Finset (Fin n))))) (Fin.castAdd n p)
            (!(Fin.append (fun p' : Fin n => decide (p' ∈ ({p} : Finset (Fin n))))
              (fun l' : Fin n => decide (l' ∈ ({l} : Finset (Fin n))))) (Fin.castAdd n p))
          = Fin.append (fun p' : Fin n => decide (p' ∈ (∅ : Finset (Fin n))))
            (fun l' : Fin n => decide (l' ∈ ({l} : Finset (Fin n)))) := by
        funext k
        refine Fin.addCases (fun p0 => ?_) (fun l0 => ?_) k
        · by_cases h : p0 = p
          · subst h
            rw [Function.update_self, Fin.append_left, Fin.append_left]
            simp
          · rw [Function.update_of_ne (fun hh => h (hinjc _ _ hh)), Fin.append_left, Fin.append_left]
            simp [h]
        · rw [Function.update_of_ne (Ne.symm (hne p l0)), Fin.append_right, Fin.append_right]
      show C.eval (List.ofFn (Function.update _ _ _)) ≠ C.eval (List.ofFn _)
      rw [U, E, E, hfalse ∅ {l} (by simp), hright l p hp]
      simp
    · obtain ⟨p, hp⟩ := hne0 l
      refine ⟨Fin.append (fun p' : Fin n => decide (p' ∈ ({p} : Finset (Fin n))))
        (fun l' : Fin n => decide (l' ∈ ({l} : Finset (Fin n)))), ?_⟩
      have U : Function.update (Fin.append (fun p' : Fin n => decide (p' ∈ ({p} : Finset (Fin n))))
            (fun l' : Fin n => decide (l' ∈ ({l} : Finset (Fin n))))) (Fin.natAdd n l)
            (!(Fin.append (fun p' : Fin n => decide (p' ∈ ({p} : Finset (Fin n))))
              (fun l' : Fin n => decide (l' ∈ ({l} : Finset (Fin n))))) (Fin.natAdd n l))
          = Fin.append (fun p' : Fin n => decide (p' ∈ ({p} : Finset (Fin n))))
            (fun l' : Fin n => decide (l' ∈ (∅ : Finset (Fin n)))) := by
        funext k
        refine Fin.addCases (fun p0 => ?_) (fun l0 => ?_) k
        · rw [Function.update_of_ne (hne p0 l), Fin.append_left, Fin.append_left]
        · by_cases h : l0 = l
          · subst h
            rw [Function.update_self, Fin.append_right, Fin.append_right]
            simp
          · rw [Function.update_of_ne (fun hh => h (hinjn _ _ hh)), Fin.append_right, Fin.append_right]
            simp [h]
      show C.eval (List.ofFn (Function.update _ _ _)) ≠ C.eval (List.ofFn _)
      rw [U, E, E, hfalse {p} ∅ (by simp), hright l p hp]
      simp
  have hd := dep_lower (n + n) _ hdep C.size hsize
  omega
