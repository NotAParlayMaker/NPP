import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1680

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem step_def (w : List Bool) (g : Gate) :
    step w g = w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)] := rfl

def V (n : ℕ) (gs : List Gate) (k : ℕ) (x : Fin n → Bool) : Bool :=
  (gs.foldl step (List.ofFn x)).getD k false

def Ok (gs : List Gate) : Prop :=
  ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

lemma len (n : ℕ) (gs : List Gate) (x : Fin n → Bool) :
    (gs.foldl step (List.ofFn x)).length = n + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp
  | append_singleton gs g ih =>
    rw [List.foldl_append]
    show (step (gs.foldl step (List.ofFn x)) g).length = _
    rw [step_def, List.length_append, ih]
    simp only [List.length_append, List.length_singleton, List.length_cons, List.length_nil] <;>
      omega

lemma V_snoc (n : ℕ) (gs : List Gate) (g : Gate) (k : ℕ) (x : Fin n → Bool) :
    V n (gs ++ [g]) k x =
      if k = n + gs.length then g.op.eval (g.inputs.map fun i => V n gs i x) else V n gs k x := by
  unfold V
  rw [List.foldl_append]
  show (step (gs.foldl step (List.ofFn x)) g).getD k false = _
  rw [step_def]
  have hl := len n gs x
  rcases lt_trichotomy k (n + gs.length) with hi | hi | hi
  · rw [List.getD_append _ _ _ _ (by rw [hl]; exact hi), if_neg hi.ne]
  · rw [List.getD_append_right _ _ _ _ (by rw [hl]; omega), hl, if_pos hi]
    subst hi
    simp
  · rw [List.getD_append_right _ _ _ _ (by rw [hl]; omega), hl, if_neg (by omega)]
    obtain ⟨k', hk⟩ : ∃ k', k - (n + gs.length) = k' + 1 := ⟨k - (n + gs.length) - 1, by omega⟩
    have e : (gs.foldl step (List.ofFn x)).getD k false = false := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [hl]; omega)]
      rfl
    rw [hk, e]
    rfl

lemma V_input (n : ℕ) (gs : List Gate) (i : Fin n) (x : Fin n → Bool) :
    V n gs i.val x = x i := by
  induction gs using List.reverseRecOn with
  | nil =>
    show (List.ofFn x).getD i.val false = x i
    rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
    simp [i.isLt]
  | append_singleton gs g ih =>
    rw [V_snoc, if_neg (by have := i.isLt; omega), ih]

lemma V_ge (n : ℕ) (gs : List Gate) (k : ℕ) (h : n + gs.length ≤ k) (x : Fin n → Bool) :
    V n gs k x = false := by
  unfold V
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [len]; exact h)]
  rfl

lemma and_rep {X : Type} (F F' : ℕ → X → Bool) (L : ℕ)
    (H : ∀ k, (∃ b : Bool, ∀ x, F k x = b) ∨ (∃ m, m < L ∧ ∀ x, F k x = F' m x))
    (l : List ℕ) :
    (∀ x, (l.map fun i => F i x).all id = false) ∨
    ∃ l' : List ℕ, l'.length ≤ l.length ∧
      ∀ x, (l.map fun i => F i x).all id = (l'.map fun i => F' i x).all id := by
  induction l with
  | nil => exact Or.inr ⟨[], le_refl _, fun x => rfl⟩
  | cons a l ih =>
    rcases ih with hb | ⟨l', hl, he⟩
    · exact Or.inl fun x => by
        show (F a x && (l.map fun i => F i x).all id) = false
        rw [hb x, Bool.and_false]
    · rcases H a with ⟨c, hc⟩ | ⟨m, _, hme⟩
      · cases c
        · exact Or.inl fun x => by
            show (F a x && (l.map fun i => F i x).all id) = false
            rw [hc x, Bool.false_and]
        · exact Or.inr ⟨l', Nat.le_succ_of_le hl, fun x => by
            show (F a x && (l.map fun i => F i x).all id) = (l'.map fun i => F' i x).all id
            rw [hc x, Bool.true_and, he x]⟩
      · exact Or.inr ⟨m :: l', Nat.succ_le_succ hl, fun x => by
          show (F a x && (l.map fun i => F i x).all id) =
            (F' m x && (l'.map fun i => F' i x).all id)
          rw [hme x, he x]⟩

lemma or_rep {X : Type} (F F' : ℕ → X → Bool) (L : ℕ)
    (H : ∀ k, (∃ b : Bool, ∀ x, F k x = b) ∨ (∃ m, m < L ∧ ∀ x, F k x = F' m x))
    (l : List ℕ) :
    (∀ x, (l.map fun i => F i x).any id = true) ∨
    ∃ l' : List ℕ, l'.length ≤ l.length ∧
      ∀ x, (l.map fun i => F i x).any id = (l'.map fun i => F' i x).any id := by
  induction l with
  | nil => exact Or.inr ⟨[], le_refl _, fun x => rfl⟩
  | cons a l ih =>
    rcases ih with hb | ⟨l', hl, he⟩
    · exact Or.inl fun x => by
        show (F a x || (l.map fun i => F i x).any id) = true
        rw [hb x, Bool.or_true]
    · rcases H a with ⟨c, hc⟩ | ⟨m, _, hme⟩
      · cases c
        · exact Or.inr ⟨l', Nat.le_succ_of_le hl, fun x => by
            show (F a x || (l.map fun i => F i x).any id) = (l'.map fun i => F' i x).any id
            rw [hc x, Bool.false_or, he x]⟩
        · exact Or.inl fun x => by
            show (F a x || (l.map fun i => F i x).any id) = true
            rw [hc x, Bool.true_or]
      · exact Or.inr ⟨m :: l', Nat.succ_le_succ hl, fun x => by
          show (F a x || (l.map fun i => F i x).any id) =
            (F' m x || (l'.map fun i => F' i x).any id)
          rw [hme x, he x]⟩

lemma gate_rep {X : Type} (F F' : ℕ → X → Bool) (L : ℕ)
    (H : ∀ k, (∃ b : Bool, ∀ x, F k x = b) ∨ (∃ m, m < L ∧ ∀ x, F k x = F' m x))
    (op : GateOp) (hop : op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (l : List ℕ) :
    (∃ b : Bool, ∀ x, op.eval (l.map fun i => F i x) = b) ∨
    ∃ l' : List ℕ, l'.length ≤ l.length ∧
      ∀ x, op.eval (l.map fun i => F i x) = op.eval (l'.map fun i => F' i x) := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with rfl | rfl | rfl
  · rcases and_rep F F' L H l with h | h
    · exact Or.inl ⟨false, h⟩
    · exact Or.inr h
  · rcases or_rep F F' L H l with h | h
    · exact Or.inl ⟨true, h⟩
    · exact Or.inr h
  · cases l with
    | nil => exact Or.inl ⟨true, fun x => rfl⟩
    | cons a l =>
      rcases H a with ⟨c, hc⟩ | ⟨m, _, hme⟩
      · exact Or.inl ⟨!c, fun x => by
          show (!(F a x)) = !c
          rw [hc x]⟩
      · exact Or.inr ⟨[m], Nat.succ_le_succ (Nat.zero_le _), fun x => by
          show (!(F a x)) = !(F' m x)
          rw [hme x]⟩

lemma main (n : ℕ) (gs : List Gate) (hF : Ok gs) :
    ∃ gs' : List Gate, Ok gs' ∧ gs'.length ≤ gs.length ∧
      ((∃ j, j < gs.length ∧
          ((∃ b : Bool, ∀ x : Fin n → Bool, V n gs (n + j) x = b) ∨
            (∃ i : Fin n, ∀ x : Fin n → Bool, V n gs (n + j) x = x i))) →
        gs'.length < gs.length) ∧
      ∀ k, (∃ b : Bool, ∀ x : Fin n → Bool, V n gs k x = b) ∨
        (∃ m, m < n + gs'.length ∧ ∀ x : Fin n → Bool, V n gs k x = V n gs' m x) := by
  induction gs using List.reverseRecOn with
  | nil =>
    refine ⟨[], hF, le_refl _, fun ⟨j, hj, _⟩ => absurd hj (by simp), fun k => ?_⟩
    by_cases hk : k < n
    · exact Or.inr ⟨k, by simpa using hk, fun x => rfl⟩
    · exact Or.inl ⟨false, fun x => V_ge n [] k (by simpa using not_lt.mp hk) x⟩
  | append_singleton gs g ih =>
    have hF1 : Ok gs := fun g' hg' => hF g' (List.mem_append_left _ hg')
    have hg := hF g (by simp)
    have hlen : (gs ++ [g]).length = gs.length + 1 := by simp
    obtain ⟨gs', hO, h1, h2, h3⟩ := ih hF1
    by_cases hbad : (∃ b : Bool, ∀ x : Fin n → Bool,
          g.op.eval (g.inputs.map fun i => V n gs i x) = b) ∨
        (∃ i : Fin n, ∀ x : Fin n → Bool,
          g.op.eval (g.inputs.map fun i => V n gs i x) = x i)
    · refine ⟨gs', hO, by omega, fun _ => by omega, fun k => ?_⟩
      by_cases hk : k = n + gs.length
      · rcases hbad with ⟨b, hb⟩ | ⟨i, hi⟩
        · exact Or.inl ⟨b, fun x => by rw [V_snoc, if_pos hk]; exact hb x⟩
        · exact Or.inr ⟨i.val, by have := i.isLt; omega, fun x => by
            rw [V_snoc, if_pos hk, V_input]; exact hi x⟩
      · rcases h3 k with ⟨b, hb⟩ | ⟨m, hm, hme⟩
        · exact Or.inl ⟨b, fun x => by rw [V_snoc, if_neg hk]; exact hb x⟩
        · exact Or.inr ⟨m, hm, fun x => by rw [V_snoc, if_neg hk]; exact hme x⟩
    · rcases gate_rep (V n gs) (V n gs') (n + gs'.length) h3 g.op hg.1 g.inputs with
        ⟨b, hb⟩ | ⟨l', hl, he⟩
      · exact absurd (Or.inl ⟨b, hb⟩) hbad
      · have hlen' : (gs' ++ [(⟨g.op, l'⟩ : Gate)]).length = gs'.length + 1 := by simp
        refine ⟨gs' ++ [⟨g.op, l'⟩], ?_, by omega, ?_, fun k => ?_⟩
        · intro g' hg'
          rcases List.mem_append.mp hg' with h | h
          · exact hO g' h
          · rw [List.mem_singleton.mp h]
            exact ⟨hg.1, le_trans hl hg.2⟩
        · rintro ⟨j, hj, hB⟩
          have : gs'.length < gs.length := by
            by_cases hjj : j = gs.length
            · exfalso
              apply hbad
              rcases hB with ⟨b, hb⟩ | ⟨i, hi⟩
              · exact Or.inl ⟨b, fun x => by
                  have h := hb x
                  rw [V_snoc, if_pos (by rw [hjj])] at h
                  exact h⟩
              · exact Or.inr ⟨i, fun x => by
                  have h := hi x
                  rw [V_snoc, if_pos (by rw [hjj])] at h
                  exact h⟩
            · refine h2 ⟨j, by omega, ?_⟩
              rcases hB with ⟨b, hb⟩ | ⟨i, hi⟩
              · exact Or.inl ⟨b, fun x => by
                  have h := hb x
                  rw [V_snoc, if_neg (by omega)] at h
                  exact h⟩
              · exact Or.inr ⟨i, fun x => by
                  have h := hi x
                  rw [V_snoc, if_neg (by omega)] at h
                  exact h⟩
          omega
        · by_cases hk : k = n + gs.length
          · exact Or.inr ⟨n + gs'.length, by omega, fun x => by
              rw [V_snoc, if_pos hk, V_snoc, if_pos rfl]; exact he x⟩
          · rcases h3 k with ⟨b, hb⟩ | ⟨m, hm, hme⟩
            · exact Or.inl ⟨b, fun x => by rw [V_snoc, if_neg hk]; exact hb x⟩
            · exact Or.inr ⟨m, by omega, fun x => by
                rw [V_snoc, if_neg hk, V_snoc, if_neg (by omega)]; exact hme x⟩

end PEqualNP.Outside.L_meta_1680

theorem PEqualNP.Outside.L_meta_1680 : ∀ (n s : ℕ) (f : (Fin n → Bool) → Bool), (∃ x y : Fin n → Bool, f x ≠ f y) → ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ s + 1 → (∀ x : Fin n → Bool, PEqualNP.MetaComplexity.circuitFun n C x = f x) → (∃ j : ℕ, j < C.gates.length ∧ ((∃ b : Bool, ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD (n + j) false = b) ∨ (∃ i : Fin n, ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD (n + j) false = x i))) → PEqualNP.MetaComplexity.HasCircuitSize n f s := by
  intro n s f hne C hC hsize hfun hex
  obtain ⟨x0, y0, hxy⟩ := hne
  obtain ⟨j, hj, hbad⟩ := hex
  obtain ⟨gs', hO, _, h2, h3⟩ := PEqualNP.Outside.L_meta_1680.main n C.gates hC
  have hlt : gs'.length < C.gates.length := h2 ⟨j, hj, hbad⟩
  have hsz : C.gates.length ≤ s + 1 := hsize
  rcases h3 C.output with ⟨b, hb⟩ | ⟨m, _, hme⟩
  · exact absurd (((hfun x0).symm.trans (hb x0)).trans ((hb y0).symm.trans (hfun y0))) hxy
  · exact ⟨⟨gs', m⟩, hO, by show gs'.length ≤ s; omega, fun x => (hme x).symm.trans (hfun x)⟩
