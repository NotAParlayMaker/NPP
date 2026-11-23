import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_698

open PEqualNP.MetaComplexity

def step (w : List Bool) (G : BinaryGate) : List Bool :=
  w ++ [G.op (w.getD G.left false) (w.getD G.right false)]

theorem foldl_length (gs : List BinaryGate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons G gs ih => rw [List.foldl_cons, ih]; simp [step]; omega

theorem foldl_getD_of_lt (gs : List BinaryGate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons G gs ih =>
    rw [List.foldl_cons, ih _ (by simp [step]; omega)]
    exact List.getD_append _ _ _ _ hi

def val (D : BinaryCircuit) (x : List Bool) (i : ℕ) : Bool :=
  (D.wires x).getD i false

-- The value an operand `o` of the gate making wire `m` reads: an earlier wire, else false.
def rd (D : BinaryCircuit) (x : List Bool) (m o : ℕ) : Bool :=
  if o < m then val D x o else false

theorem rd_of_lt (D : BinaryCircuit) (x : List Bool) (m o : ℕ) (h : o < m) :
    rd D x m o = val D x o := by simp [rd, h]

theorem eq_not_of_ne : ∀ p q : Bool, ¬ p = q → q = !p := by decide

theorem wires_eq (D : BinaryCircuit) (x : List Bool) : D.wires x = D.gates.foldl step x := rfl

theorem val_input (D : BinaryCircuit) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    val D x i = x.getD i false := by
  unfold val; rw [wires_eq]; exact foldl_getD_of_lt _ _ _ hi

theorem val_out (D : BinaryCircuit) (x : List Bool) (i : ℕ)
    (hi : x.length + D.gates.length ≤ i) : val D x i = false := by
  unfold val; rw [wires_eq]
  exact List.getD_eq_default _ _ (by rw [foldl_length]; omega)

theorem val_gate (D : BinaryCircuit) (x : List Bool) (j : ℕ) (G : BinaryGate)
    (hG : D.gates[j]? = some G) :
    val D x (x.length + j) =
      G.op (rd D x (x.length + j) G.left) (rd D x (x.length + j) G.right) := by
  have hj : j < D.gates.length := by
    by_contra h; rw [List.getElem?_eq_none (by omega)] at hG; cases hG
  have hGj : D.gates[j] = G := by rw [List.getElem?_eq_getElem hj] at hG; exact Option.some.inj hG
  obtain ⟨P, hP⟩ : ∃ P, P = (D.gates.take j).foldl step x := ⟨_, rfl⟩
  have hPlen : P.length = x.length + j := by
    rw [hP, foldl_length, List.length_take]; omega
  have hlist : D.gates = D.gates.take j ++ G :: D.gates.drop (j + 1) := by
    conv_lhs => rw [← List.take_append_drop j D.gates]
    rw [List.drop_eq_getElem_cons hj, hGj]
  have hsplit : D.wires x = (D.gates.drop (j + 1)).foldl step (step P G) := by
    rw [wires_eq]
    conv_lhs => rw [hlist]
    rw [List.foldl_append, List.foldl_cons, hP]
  have hstep : (step P G).length = x.length + j + 1 := by simp [step, hPlen]
  have hread : ∀ o, P.getD o false = rd D x (x.length + j) o := by
    intro o
    unfold rd
    split_ifs with ho
    · unfold val
      rw [hsplit, foldl_getD_of_lt (D.gates.drop (j + 1)) (step P G) o (by omega)]
      exact (List.getD_append _ _ _ _ (by omega)).symm
    · exact List.getD_eq_default _ _ (by omega)
  unfold val
  rw [hsplit, foldl_getD_of_lt (D.gates.drop (j + 1)) (step P G) (x.length + j) (by omega),
    ← hread, ← hread, ← hPlen]
  simp [step]

-- Two inputs agree outside an exempt set `E` of wires; every gate outside `E` either reads no
-- earlier wire of `E` or is known to agree. Then every wire outside `E` agrees.
theorem agree (D : BinaryCircuit) (n : ℕ) (X X' : List Bool) (hX : X.length = n)
    (hX' : X'.length = n) (E : ℕ → Prop)
    (hin : ∀ i < n, ¬ E i → X.getD i false = X'.getD i false)
    (hgate : ∀ j G, D.gates[j]? = some G → ¬ E (n + j) →
      ((G.left < n + j → ¬ E G.left) ∧ (G.right < n + j → ¬ E G.right)) ∨
        val D X (n + j) = val D X' (n + j)) :
    ∀ i, ¬ E i → val D X i = val D X' i := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
  intro hi
  by_cases hin' : i < n
  · rw [val_input _ _ _ (by omega), val_input _ _ _ (by omega)]
    exact hin i hin' hi
  obtain ⟨j, rfl⟩ : ∃ j, i = n + j := ⟨i - n, by omega⟩
  by_cases hj : j < D.gates.length
  · have hG := List.getElem?_eq_getElem hj
    rcases hgate j _ hG hi with ⟨hl, hr⟩ | heq
    · have hrd : ∀ o, (o < n + j → ¬ E o) →
          rd D X (n + j) o = rd D X' (n + j) o := by
        intro o ho
        unfold rd
        split_ifs with h
        · exact ih o h (ho h)
        · rfl
      have h1 := val_gate D X j _ hG
      have h2 := val_gate D X' j _ hG
      rw [hX] at h1; rw [hX'] at h2
      rw [h1, h2, hrd _ hl, hrd _ hr]
    · exact heq
  · rw [val_out _ _ _ (by omega), val_out _ _ _ (by omega)]

theorem getD_ofFn {n : ℕ} (y : Fin n → Bool) (i : ℕ) (hi : i < n) :
    (List.ofFn y).getD i false = y ⟨i, hi⟩ := by
  simp [List.getD_eq_getElem?_getD, hi]

theorem main (n : ℕ) (D : BinaryCircuit) (v u : Fin n) (g h k : ℕ) (hvu : v ≠ u) (hgh : g ≠ h)
    (hg : ∀ j : ℕ, (∃ G : BinaryGate, D.gates[j]? = some G ∧
      (G.left = v.val ∨ G.right = v.val)) ↔ j = g)
    (hh : ∀ j : ℕ, (∃ G : BinaryGate, D.gates[j]? = some G ∧
      (G.left = u.val ∨ G.right = u.val)) ↔ j = h)
    (hk1 : ∀ j : ℕ, (∃ G : BinaryGate, D.gates[j]? = some G ∧
      (G.left = n + g ∨ G.right = n + g) ∧ g < j) ↔ j = k)
    (hk2 : ∀ j : ℕ, (∃ G : BinaryGate, D.gates[j]? = some G ∧
      (G.left = n + h ∨ G.right = n + h) ∧ h < j) ↔ j = k)
    (hxor : ∃ G : BinaryGate, D.gates[k]? = some G ∧
      ((G.op false false = false ∧ G.op false true = true ∧ G.op true false = true ∧
        G.op true true = false) ∨
       (G.op false false = true ∧ G.op false true = false ∧ G.op true false = false ∧
        G.op true true = true)))
    (ho1 : D.output ≠ v.val) (ho2 : D.output ≠ u.val) (ho3 : D.output ≠ n + g)
    (ho4 : D.output ≠ n + h) (x : Fin n → Bool) (f : Bool → Bool → Bool)
    (hf : ∀ a b : Bool, f a b = D.eval (List.ofFn (Function.update (Function.update x v a) u b))) :
    f false false = f true true ∨ (∀ a b : Bool, f a b = f (!a) b) ∨
      (∀ a b : Bool, f a b = f a (!b)) := by
  classical
  set X : Bool → Bool → List Bool :=
    fun a b => List.ofFn (Function.update (Function.update x v a) u b) with hXdef
  have hXlen : ∀ a b, (X a b).length = n := by intro a b; simp [hXdef]
  have hXin : ∀ a b i (hi : i < n), (X a b).getD i false =
      Function.update (Function.update x v a) u b ⟨i, hi⟩ := by
    intro a b i hi; exact getD_ofFn _ _ hi
  have hfv : ∀ a b, f a b = val D (X a b) D.output := fun a b => hf a b
  -- Gate `k` reads exactly the wires `n + g` and `n + h`, after both.
  obtain ⟨Gk, hGk, hkg, hgk⟩ := (hk1 k).2 rfl
  obtain ⟨Gk', hGk', hkh, hhk⟩ := (hk2 k).2 rfl
  rw [hGk] at hGk'
  cases Option.some.inj hGk'
  obtain ⟨Gx, hGx, hop⟩ := hxor
  rw [hGk] at hGx
  cases Option.some.inj hGx
  have hngh : n + g ≠ n + h := by omega
  have hops : (Gk.left = n + g ∧ Gk.right = n + h) ∨ (Gk.left = n + h ∧ Gk.right = n + g) := by
    rcases hkg with h1 | h1 <;> rcases hkh with h2 | h2
    · exact absurd (h1.symm.trans h2) hngh
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr ⟨h2, h1⟩
    · exact absurd (h1.symm.trans h2) hngh
  -- Facts about who reads what.
  have readv : ∀ j G, D.gates[j]? = some G → G.left = v.val ∨ G.right = v.val → j = g :=
    fun j G hG hr => (hg j).1 ⟨G, hG, hr⟩
  have readu : ∀ j G, D.gates[j]? = some G → G.left = u.val ∨ G.right = u.val → j = h :=
    fun j G hG hr => (hh j).1 ⟨G, hG, hr⟩
  have readg : ∀ j G, D.gates[j]? = some G → G.left = n + g ∨ G.right = n + g → g < j →
      j = k := fun j G hG hr hlt => (hk1 j).1 ⟨G, hG, hr, hlt⟩
  have readh : ∀ j G, D.gates[j]? = some G → G.left = n + h ∨ G.right = n + h → h < j →
      j = k := fun j G hG hr hlt => (hk2 j).1 ⟨G, hG, hr, hlt⟩
  have hvn : v.val < n := v.isLt
  have hun : u.val < n := u.isLt
  have hvu' : v.val ≠ u.val := fun e => hvu (Fin.ext e)
  -- The wire `n + g` does not depend on `b`.
  have hG_b : ∀ a b b', val D (X a b) (n + g) = val D (X a b') (n + g) := by
    intro a b b'
    refine agree D n (X a b) (X a b') (hXlen a b) (hXlen a b')
      (fun w => w = u.val ∨ w = n + h ∨ n + k ≤ w) ?_ ?_ (n + g) (by omega)
    · intro i hi hE
      have hiu : (⟨i, hi⟩ : Fin n) ≠ u := fun e => hE (Or.inl (congrArg Fin.val e))
      rw [hXin a b i hi, hXin a b' i hi, Function.update_of_ne hiu, Function.update_of_ne hiu]
    · intro j G hG hE
      have hjh : j ≠ h := fun e => hE (Or.inr (Or.inl (by omega)))
      have hjk : j < k := by omega
      left
      constructor
      · intro hl hEl
        rcases hEl with e | e | e
        · exact hjh (readu j G hG (Or.inl e))
        · exact absurd (readh j G hG (Or.inl e) (by omega)) (by omega)
        · omega
      · intro hr hEr
        rcases hEr with e | e | e
        · exact hjh (readu j G hG (Or.inr e))
        · exact absurd (readh j G hG (Or.inr e) (by omega)) (by omega)
        · omega
  -- The wire `n + h` does not depend on `a`.
  have hH_a : ∀ a a' b, val D (X a b) (n + h) = val D (X a' b) (n + h) := by
    intro a a' b
    refine agree D n (X a b) (X a' b) (hXlen a b) (hXlen a' b)
      (fun w => w = v.val ∨ w = n + g ∨ n + k ≤ w) ?_ ?_ (n + h) (by omega)
    · intro i hi hE
      have hiv : (⟨i, hi⟩ : Fin n) ≠ v := fun e => hE (Or.inl (congrArg Fin.val e))
      rw [hXin a b i hi, hXin a' b i hi]
      by_cases hiu : (⟨i, hi⟩ : Fin n) = u
      · rw [hiu, Function.update_self, Function.update_self]
      · rw [Function.update_of_ne hiu, Function.update_of_ne hiu, Function.update_of_ne hiv,
          Function.update_of_ne hiv]
    · intro j G hG hE
      have hjg : j ≠ g := fun e => hE (Or.inr (Or.inl (by omega)))
      have hjk : j < k := by omega
      left
      constructor
      · intro hl hEl
        rcases hEl with e | e | e
        · exact hjg (readv j G hG (Or.inl e))
        · exact absurd (readg j G hG (Or.inl e) (by omega)) (by omega)
        · omega
      · intro hr hEr
        rcases hEr with e | e | e
        · exact hjg (readv j G hG (Or.inr e))
        · exact absurd (readg j G hG (Or.inr e) (by omega)) (by omega)
        · omega
  -- Inputs other than `v` and `u` agree between any two settings.
  have hin2 : ∀ a b a' b' i (hi : i < n), ¬ (i = v.val ∨ i = u.val) →
      (X a b).getD i false = (X a' b').getD i false := by
    intro a b a' b' i hi hE
    have hiv : (⟨i, hi⟩ : Fin n) ≠ v := fun e => hE (Or.inl (congrArg Fin.val e))
    have hiu : (⟨i, hi⟩ : Fin n) ≠ u := fun e => hE (Or.inr (congrArg Fin.val e))
    rw [hXin a b i hi, hXin a' b' i hi, Function.update_of_ne hiu, Function.update_of_ne hiu,
      Function.update_of_ne hiv, Function.update_of_ne hiv]
  -- Equal values at `n + g` and `n + h` give equal outputs.
  have hsame : ∀ a b a' b', val D (X a b) (n + g) = val D (X a' b') (n + g) →
      val D (X a b) (n + h) = val D (X a' b') (n + h) → f a b = f a' b' := by
    intro a b a' b' eg eh
    rw [hfv, hfv]
    refine agree D n (X a b) (X a' b') (hXlen a b) (hXlen a' b')
      (fun w => w = v.val ∨ w = u.val) (hin2 a b a' b') ?_ D.output (by tauto)
    intro j G hG _
    by_cases hjg : j = g
    · subst hjg; exact Or.inr eg
    by_cases hjh : j = h
    · subst hjh; exact Or.inr eh
    left
    constructor
    · intro _ hEl
      rcases hEl with e | e
      · exact hjg (readv j G hG (Or.inl e))
      · exact hjh (readu j G hG (Or.inl e))
    · intro _ hEr
      rcases hEr with e | e
      · exact hjg (readv j G hG (Or.inr e))
      · exact hjh (readu j G hG (Or.inr e))
  -- Flipping both values at `n + g` and `n + h` leaves the output unchanged.
  have hflip : ∀ a b a' b', val D (X a' b') (n + g) = !val D (X a b) (n + g) →
      val D (X a' b') (n + h) = !val D (X a b) (n + h) → f a b = f a' b' := by
    intro a b a' b' eg eh
    rw [hfv, hfv]
    refine agree D n (X a b) (X a' b') (hXlen a b) (hXlen a' b')
      (fun w => w = v.val ∨ w = u.val ∨ w = n + g ∨ w = n + h) ?_ ?_ D.output (by tauto)
    · intro i hi hE; exact hin2 a b a' b' i hi (by tauto)
    · intro j G hG hE
      have hjg : j ≠ g := fun e => hE (Or.inr (Or.inr (Or.inl (by omega))))
      have hjh : j ≠ h := fun e => hE (Or.inr (Or.inr (Or.inr (by omega))))
      by_cases hjk : j = k
      · subst hjk
        right
        rw [hGk] at hG
        cases Option.some.inj hG
        have h1 := val_gate D (X a b) j Gk hGk
        have h2 := val_gate D (X a' b') j Gk hGk
        rw [hXlen] at h1 h2
        rw [h1, h2]
        generalize hp : val D (X a b) (n + g) = p at eg
        generalize hq : val D (X a b) (n + h) = q at eh
        rcases hops with ⟨hl, hr⟩ | ⟨hl, hr⟩ <;>
          · rw [hl, hr, rd_of_lt _ _ _ _ (by omega), rd_of_lt _ _ _ _ (by omega),
              rd_of_lt _ _ _ _ (by omega), rd_of_lt _ _ _ _ (by omega), eg, eh, hp, hq]
            cases p <;> cases q <;>
              rcases hop with ⟨o1, o2, o3, o4⟩ | ⟨o1, o2, o3, o4⟩ <;>
              simp only [Bool.not_true, Bool.not_false, o1, o2, o3, o4]
      · left
        constructor
        · intro hl hEl
          rcases hEl with e | e | e | e
          · exact hjg (readv j G hG (Or.inl e))
          · exact hjh (readu j G hG (Or.inl e))
          · exact hjk (readg j G hG (Or.inl e) (by omega))
          · exact hjk (readh j G hG (Or.inl e) (by omega))
        · intro hr hEr
          rcases hEr with e | e | e | e
          · exact hjg (readv j G hG (Or.inr e))
          · exact hjh (readu j G hG (Or.inr e))
          · exact hjk (readg j G hG (Or.inr e) (by omega))
          · exact hjk (readh j G hG (Or.inr e) (by omega))
  -- The three cases.
  by_cases hα : val D (X false false) (n + g) = val D (X true false) (n + g)
  · right; left
    intro a b
    apply hsame
    · rw [hG_b a b false, hG_b (!a) b false]
      cases a
      · exact hα
      · exact hα.symm
    · exact hH_a a (!a) b
  by_cases hβ : val D (X false false) (n + h) = val D (X false true) (n + h)
  · right; right
    intro a b
    apply hsame
    · exact hG_b a b (!b)
    · rw [hH_a a false b, hH_a a false (!b)]
      cases b
      · exact hβ
      · exact hβ.symm
  · left
    apply hflip
    · rw [hG_b true true false]
      exact eq_not_of_ne _ _ hα
    · rw [hH_a true false true]
      exact eq_not_of_ne _ _ hβ

end PEqualNP.Outside.L_meta_698

theorem PEqualNP.Outside.L_meta_698 : ∀ (n : ℕ) (D : PEqualNP.MetaComplexity.BinaryCircuit) (v u : Fin n) (g h k : ℕ), v ≠ u → g ≠ h → (∀ j : ℕ, (∃ G : PEqualNP.MetaComplexity.BinaryGate, D.gates[j]? = some G ∧ (G.left = v.val ∨ G.right = v.val)) ↔ j = g) → (∀ j : ℕ, (∃ G : PEqualNP.MetaComplexity.BinaryGate, D.gates[j]? = some G ∧ (G.left = u.val ∨ G.right = u.val)) ↔ j = h) → (∃ G : PEqualNP.MetaComplexity.BinaryGate, D.gates[g]? = some G ∧ ¬ (G.left = v.val ∧ G.right = v.val)) → (∃ G : PEqualNP.MetaComplexity.BinaryGate, D.gates[h]? = some G ∧ ¬ (G.left = u.val ∧ G.right = u.val)) → (∀ j : ℕ, (∃ G : PEqualNP.MetaComplexity.BinaryGate, D.gates[j]? = some G ∧ (G.left = n + g ∨ G.right = n + g) ∧ g < j) ↔ j = k) → (∀ j : ℕ, (∃ G : PEqualNP.MetaComplexity.BinaryGate, D.gates[j]? = some G ∧ (G.left = n + h ∨ G.right = n + h) ∧ h < j) ↔ j = k) → (∃ G : PEqualNP.MetaComplexity.BinaryGate, D.gates[k]? = some G ∧ ((G.op false false = false ∧ G.op false true = true ∧ G.op true false = true ∧ G.op true true = false) ∨ (G.op false false = true ∧ G.op false true = false ∧ G.op true false = false ∧ G.op true true = true))) → D.output ≠ v.val → D.output ≠ u.val → D.output ≠ n + g → D.output ≠ n + h → ∀ (x : Fin n → Bool) (f : Bool → Bool → Bool), (∀ a b : Bool, f a b = D.eval (List.ofFn (Function.update (Function.update x v a) u b))) → (f false false = f true true ∨ (∀ a b : Bool, f a b = f (!a) b) ∨ (∀ a b : Bool, f a b = f a (!b))) := by
  intro n D v u g h k hvu hgh hg hh _ _ hk1 hk2 hxor ho1 ho2 ho3 ho4 x f hf
  exact PEqualNP.Outside.L_meta_698.main n D v u g h k hvu hgh hg hh hk1 hk2 hxor ho1 ho2 ho3 ho4 x f hf
