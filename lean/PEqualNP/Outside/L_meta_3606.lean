import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3606

open PEqualNP.CircuitLowerBounds

def stepF (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl stepF x := rfl

def BLe (w w' : List Bool) : Prop :=
  w.length = w'.length ∧ ∀ i, w.getD i false = true → w'.getD i false = true

lemma getD_snoc (w : List Bool) (b : Bool) (i : ℕ) :
    (w ++ [b]).getD i false =
      if i < w.length then w.getD i false else if i = w.length then b else false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append]
  split_ifs with h1 h2
  · rfl
  · subst h2; simp
  · have : 0 < i - w.length := by omega
    simp [List.getElem?_singleton, show i - w.length ≠ 0 by omega]

lemma eval_mono (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or) (w w' : List Bool)
    (h : ∀ i, w.getD i false = true → w'.getD i false = true) :
    g.op.eval (g.inputs.map fun i => w.getD i false) = true →
      g.op.eval (g.inputs.map fun i => w'.getD i false) = true := by
  rcases hg with hg | hg <;> rw [hg] <;> simp only [GateOp.eval, List.all_map, List.any_map,
    List.all_eq_true, List.any_eq_true, Function.comp_apply, id_eq]
  · intro hh i hi; exact h i (hh i hi)
  · rintro ⟨i, hi, hh⟩; exact ⟨i, hi, h i hh⟩

lemma step_mono (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or) (w w' : List Bool)
    (h : BLe w w') : BLe (stepF w g) (stepF w' g) := by
  obtain ⟨hl, hv⟩ := h
  refine ⟨by simp [stepF, hl], fun i hi => ?_⟩
  unfold stepF at hi ⊢
  rw [getD_snoc] at hi ⊢
  rw [← hl]
  split_ifs at hi ⊢ with h1 h2
  · exact hv i hi
  · exact eval_mono g hg w w' hv hi

lemma foldl_mono (gs : List Gate) (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ w w' : List Bool, BLe w w' → BLe (gs.foldl stepF w) (gs.foldl stepF w') := by
  induction gs with
  | nil => intro w w' h; exact h
  | cons g gs ih =>
    intro w w' h
    simp only [List.foldl_cons]
    exact ih (fun g' hg' => hgs g' (List.mem_cons_of_mem g hg')) _ _
      (step_mono g (hgs g (List.mem_cons_self)) w w' h)

lemma foldl_length (gs : List Gate) :
    ∀ w : List Bool, (gs.foldl stepF w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp
  | cons g gs ih =>
    intro w
    simp only [List.foldl_cons, ih, stepF, List.length_append, List.length_cons,
      List.length_singleton, List.length_nil]
    omega

lemma ofFn_le {n : ℕ} (x y : Fin n → Bool) (h : ∀ i, x i = true → y i = true) :
    BLe (List.ofFn x) (List.ofFn y) := by
  refine ⟨by simp, fun i hi => ?_⟩
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn] at hi ⊢
  by_cases hin : i < n
  · simp only [hin, Option.getD_some, List.ofFnNthVal, dite_true] at hi ⊢
    exact h _ hi
  · simp [hin] at hi

lemma headD_map_mono (is : List ℕ) (w w' : List Bool)
    (h : ∀ i, w.getD i false = true → w'.getD i false = true) :
    (is.map fun i => w.getD i false).headD false = true →
      (is.map fun i => w'.getD i false).headD false = true := by
  cases is with
  | nil => simp
  | cons i is => simp only [List.map_cons, List.headD_cons]; exact h i

lemma key (pre mid : List Gate) (g2 g3 : Gate)
    (hpre : ∀ g ∈ pre, g.op = GateOp.and ∨ g.op = GateOp.or)
    (hmid : ∀ g ∈ mid, g.op = GateOp.and ∨ g.op = GateOp.or)
    (h2 : g2.op = GateOp.not) (h3 : g3.op = GateOp.not)
    (C : Circuit) (hC : C = ⟨pre ++ g2 :: (mid ++ [g3]), 9 + (pre.length + 1 + mid.length)⟩)
    (f0 : PEqualNP.MetaComplexity.circuitFun 9 C (fun _ => false) = false)
    (f1 : PEqualNP.MetaComplexity.circuitFun 9 C (fun _ => true) = true) :
    ∀ x : Fin 9 → Bool, PEqualNP.MetaComplexity.circuitFun 9 C x =
      (pre.foldl stepF (List.ofFn x)).getD (g2.inputs.headD (9 + pre.length)) false := by
  set P : (Fin 9 → Bool) → List Bool := fun x => pre.foldl stepF (List.ofFn x) with hP
  set j := g2.inputs.headD (9 + pre.length) with hj
  set m : (Fin 9 → Bool) → Bool := fun x => (P x).getD j false with hm
  have hPlen : ∀ x, (P x).length = 9 + pre.length := by
    intro x; simp [hP, foldl_length]
  have hPmono : ∀ x y : Fin 9 → Bool, (∀ i, x i = true → y i = true) → BLe (P x) (P y) :=
    fun x y h => foldl_mono pre hpre _ _ (ofFn_le x y h)
  have hg2 : ∀ x, g2.op.eval (g2.inputs.map fun i => (P x).getD i false) = !m x := by
    intro x
    rw [h2]
    simp only [GateOp.eval, hm, hj]
    cases hin : g2.inputs with
    | nil =>
      simp only [List.map_nil, List.headD_nil]
      have : (P x).getD (9 + pre.length) false = false := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [hPlen])]
        rfl
      rw [this]
    | cons i is => simp
  set W : (Fin 9 → Bool) → Bool → List Bool := fun x a => mid.foldl stepF (P x ++ [a]) with hW
  have hWlen : ∀ x a, (W x a).length = 9 + (pre.length + 1 + mid.length) := by
    intro x a; simp only [hW, foldl_length, List.length_append, hPlen, List.length_singleton]
    omega
  set h : (Fin 9 → Bool) → Bool → Bool :=
    fun x a => (g3.inputs.map fun i => (W x a).getD i false).headD false with hh
  have hmono_m : ∀ x y : Fin 9 → Bool, (∀ i, x i = true → y i = true) →
      m x = true → m y = true := fun x y hxy => (hPmono x y hxy).2 j
  have hmono_h : ∀ (x y : Fin 9 → Bool) (a b : Bool), (∀ i, x i = true → y i = true) →
      (a = true → b = true) → h x a = true → h y b = true := by
    intro x y a b hxy hab
    apply headD_map_mono
    apply (foldl_mono mid hmid _ _ _).2
    obtain ⟨hl, hv⟩ := hPmono x y hxy
    refine ⟨by simp [hl], fun i hi => ?_⟩
    rw [getD_snoc] at hi ⊢
    rw [← hl]
    split_ifs at hi ⊢
    · exact hv i hi
    · exact hab hi
  have hf : ∀ x, PEqualNP.MetaComplexity.circuitFun 9 C x = !h x (!m x) := by
    intro x
    subst hC
    simp only [PEqualNP.MetaComplexity.circuitFun, Circuit.eval, wires_eq, List.foldl_append,
      List.foldl_cons]
    have e1 : stepF (List.foldl stepF (List.ofFn x) pre) g2 = P x ++ [!m x] := by
      simp only [stepF]; rw [← hg2 x]
    rw [e1]
    have e2 : (stepF (List.foldl stepF (P x ++ [!m x]) mid) g3) =
        W x (!m x) ++ [!h x (!m x)] := by
      simp only [stepF, hh, hW]
      rw [h3]; rfl
    rw [e2, List.foldl_nil, getD_snoc]
    simp [hWlen]
  have A0 : h (fun _ => false) (!m (fun _ => false)) = true := by
    have := hf (fun _ => false); rw [f0] at this
    cases hv : h (fun _ => false) (!m (fun _ => false)) with
    | false => rw [hv] at this; exact absurd this (by decide)
    | true => rfl
  have A1 : h (fun _ => true) (!m (fun _ => true)) = false := by
    have := hf (fun _ => true); rw [f1] at this
    cases hv : h (fun _ => true) (!m (fun _ => true)) with
    | false => rfl
    | true => rw [hv] at this; exact absurd this (by decide)
  have hle0 : ∀ y : Fin 9 → Bool, ∀ i, (fun _ => false : Fin 9 → Bool) i = true → y i = true := by
    intro y i hi; simp at hi
  have hle1 : ∀ y : Fin 9 → Bool, ∀ i, y i = true → (fun _ => true : Fin 9 → Bool) i = true := by
    intro y i _; rfl
  have m0 : m (fun _ => false) = false := by
    cases hm0 : m (fun _ => false)
    · rfl
    · exfalso
      have hm1 : m (fun _ => true) = true := hmono_m _ _ (hle0 _) hm0
      rw [hm0] at A0; rw [hm1] at A1
      simp only [Bool.not_true, Bool.not_false] at A0 A1
      have := hmono_h (fun _ => false) (fun _ => true) false false (hle0 _) id A0
      rw [A1] at this; exact Bool.false_ne_true this
  have m1 : m (fun _ => true) = true := by
    cases hm1 : m (fun _ => true)
    · exfalso
      rw [m0] at A0; rw [hm1] at A1
      simp only [Bool.not_true, Bool.not_false] at A0 A1
      have := hmono_h (fun _ => false) (fun _ => true) true true (hle0 _) id A0
      rw [A1] at this; exact Bool.false_ne_true this
    · rfl
  rw [m0] at A0; rw [m1] at A1
  simp only [Bool.not_true, Bool.not_false] at A0 A1
  intro x
  rw [hf x]
  show (!h x (!m x)) = m x
  cases hmx : m x
  · have := hmono_h (fun _ => false) x true true (hle0 x) id A0
    simp [this]
  · simp only [Bool.not_true]
    cases hx : h x false
    · rfl
    · have := hmono_h x (fun _ => true) false false (hle1 x) id hx
      rw [A1] at this; exact absurd this Bool.false_ne_true

end PEqualNP.Outside.L_meta_3606

open PEqualNP.CircuitLowerBounds

theorem PEqualNP.Outside.L_meta_3606 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : Fin x1.gates.length), PEqualNP.MetaComplexity.FanInTwo x1 → x2 < x3 → ↑x3 + (1 : ℕ) = x1.size → x1.output = (9 : ℕ) + ↑x3 → (x1.gates.get x2).op = PEqualNP.CircuitLowerBounds.GateOp.not → (x1.gates.get x3).op = PEqualNP.CircuitLowerBounds.GateOp.not → (∀ (x10 : Fin x1.gates.length), (x1.gates.get x10).op = PEqualNP.CircuitLowerBounds.GateOp.not → x10 = x2 ∨ x10 = x3) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 fun (x11 : Fin (9 : ℕ)) => Bool.false) = Bool.false → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 fun (x12 : Fin (9 : ℕ)) => Bool.true) = Bool.true → ∃ (x13 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x13 ∧ x13.size ≤ ↑x2 ∧ PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x13 = PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 := by
  rintro ⟨gs, out⟩ a b hfan hab hsize hout h2 h3 huniq f0 f1
  simp only [PEqualNP.CircuitLowerBounds.Circuit.size] at hsize hout h2 h3 huniq
  simp only at a b hab
  have hab' : a.val < b.val := hab
  have hlen : gs.length = b.val + 1 := hsize.symm
  set pre := gs.take a.val with hpre
  set mid := (gs.drop (a.val + 1)).take (b.val - (a.val + 1)) with hmid
  have hpl : pre.length = a.val := by simp [hpre]
  have hml : mid.length = b.val - (a.val + 1) := by simp [hmid]
  have hdec : gs = pre ++ gs[a.val] :: (mid ++ [gs[b.val]]) := by
    apply List.ext_getElem
    · simp [hpl, hml]; omega
    · intro i h1 h2'
      rw [List.getElem_append]
      split_ifs with hi
      · simp [hpre]
      · rw [List.getElem_cons]
        split_ifs with hi2
        · simp [hpl] at hi2 ⊢; congr 1; omega
        · rw [List.getElem_append]
          split_ifs with hi3
          · simp [hmid]; congr 1; simp [hpl] at hi3 hi2 ⊢; omega
          · simp [hpl, hml] at hi3 hi2 h2' ⊢
            congr 1; omega
  have hnot : ∀ (i : ℕ) (hi : i < gs.length), i ≠ a.val → i ≠ b.val →
      gs[i].op = GateOp.and ∨ gs[i].op = GateOp.or := by
    intro i hi hia hib
    have hm := (hfan gs[i] (List.getElem_mem hi)).1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm
    rcases hm with hm | hm | hm
    · exact Or.inl hm
    · exact Or.inr hm
    · exfalso
      rcases huniq ⟨i, hi⟩ hm with h | h
      · exact hia (congrArg Fin.val h)
      · exact hib (congrArg Fin.val h)
  have hpre' : ∀ g ∈ pre, g.op = GateOp.and ∨ g.op = GateOp.or := by
    intro g hg
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hg
    rw [hpl] at hi
    simp only [hpre, List.getElem_take]
    exact hnot i (by omega) (by omega) (by omega)
  have hmid' : ∀ g ∈ mid, g.op = GateOp.and ∨ g.op = GateOp.or := by
    intro g hg
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hg
    rw [hml] at hi
    simp only [hmid, List.getElem_take, List.getElem_drop]
    exact hnot _ (by omega) (by omega) (by omega)
  have hC : (⟨gs, out⟩ : Circuit) =
      ⟨pre ++ gs[a.val] :: (mid ++ [gs[b.val]]), 9 + (pre.length + 1 + mid.length)⟩ := by
    rw [hpl, hml]
    refine (Circuit.mk.injEq _ _ _ _).mpr ⟨hdec, ?_⟩
    omega
  refine ⟨⟨pre, (gs[a.val]).inputs.headD (9 + pre.length)⟩, ?_, ?_, ?_⟩
  · intro g hg
    exact hfan g (List.mem_of_mem_take hg)
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size, hpl]
  · funext x
    rw [PEqualNP.Outside.L_meta_3606.key pre mid gs[a.val] gs[b.val] hpre' hmid' h2 h3 _ hC
      f0 f1 x]
    rfl
