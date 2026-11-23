import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_698_aux
open PEqualNP.MetaComplexity

def step (w : List Bool) (g : BinaryGate) : List Bool :=
  w ++ [g.op (w.getD g.left false) (w.getD g.right false)]

lemma keep (gs : List BinaryGate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih (step w g) (by simp [step]; omega)]
    exact List.getD_append w _ false i hi

lemma run_length (gs : List BinaryGate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => simp only [List.foldl_cons, ih, step, List.length_append,
      List.length_cons, List.length_nil]; omega

lemma gate_value (gs : List BinaryGate) (w : List Bool) (j : ℕ) (g : BinaryGate)
    (hj : gs[j]? = some g) :
    (gs.foldl step w).getD (w.length+j) false = g.op
      (if g.left < w.length+j then (gs.foldl step w).getD g.left false else false)
      (if g.right < w.length+j then (gs.foldl step w).getD g.right false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons k gs ih =>
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
      subst k
      simp only [Nat.add_zero, List.foldl_cons]
      rw [keep gs (step w g) w.length (by simp [step])]
      have hs : ∀ i, w.getD i false =
          if i < w.length then (gs.foldl step (step w g)).getD i false else false := by
        intro i
        by_cases hi : i < w.length
        · rw [if_pos hi, keep gs (step w g) i (by simp [step]; omega)]
          exact (List.getD_append w _ false i hi).symm
        · rw [if_neg hi, List.getD_eq_default _ _ (by omega)]
      simpa [step, List.getD] using congrArg₂ g.op (hs g.left) (hs g.right)
    | succ j =>
      simp only [List.getElem?_cons_succ] at hj
      have h := ih (step w k) j hj
      simpa [step, List.foldl_cons, Nat.add_assoc, Nat.add_comm 1 j] using h

def val {n : ℕ} (D : BinaryCircuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (D.wires (List.ofFn x)).getD w false

lemma val_input {n : ℕ} (D : BinaryCircuit) (x : Fin n → Bool) (i : Fin n) :
    val D x i = x i := by
  unfold val BinaryCircuit.wires
  rw [show (fun w g => w ++ [g.op (w.getD g.left false) (w.getD g.right false)]) = step from rfl]
  rw [keep _ _ _ (by simpa using i.isLt)]
  simp

lemma val_beyond {n : ℕ} (D : BinaryCircuit) (x : Fin n → Bool) (w : ℕ)
    (hw : n + D.gates.length ≤ w) : val D x w = false := by
  unfold val BinaryCircuit.wires
  apply List.getD_eq_default
  change (D.gates.foldl step (List.ofFn x)).length ≤ w
  simpa only [run_length, List.length_ofFn] using hw

lemma val_gate {n : ℕ} (D : BinaryCircuit) (x : Fin n → Bool) (j : ℕ) (g : BinaryGate)
    (hj : D.gates[j]? = some g) :
    val D x (n+j) = g.op
      (if g.left < n+j then val D x g.left else false)
      (if g.right < n+j then val D x g.right else false) := by
  change (D.gates.foldl step (List.ofFn x)).getD (n+j) false = _
  change _ = g.op
    (if g.left < n+j then (D.gates.foldl step (List.ofFn x)).getD g.left false else false)
    (if g.right < n+j then (D.gates.foldl step (List.ofFn x)).getD g.right false else false)
  simpa only [List.length_ofFn] using gate_value D.gates (List.ofFn x) j g hj

lemma agree {n : ℕ} (D : BinaryCircuit) (x y : Fin n → Bool) (B : ℕ → Prop) (t : ℕ)
    (hin : ∀ i : Fin n, ¬ B i → x i = y i)
    (hgate : ∀ j G, D.gates[j]? = some G → ¬ B (n+j) → n+j < t →
      val D x (n+j) = val D y (n+j) ∨
        ((G.left < n+j → ¬ B G.left) ∧ (G.right < n+j → ¬ B G.right))) :
    ∀ w, w < t → ¬ B w → val D x w = val D y w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hwt hB
    by_cases hwn : w < n
    · calc
        val D x w = x ⟨w,hwn⟩ := val_input D x ⟨w,hwn⟩
        _ = y ⟨w,hwn⟩ := hin ⟨w,hwn⟩ hB
        _ = val D y w := (val_input D y ⟨w,hwn⟩).symm
    · by_cases hwl : w < n+D.gates.length
      · have hj : w-n < D.gates.length := by omega
        let G := D.gates[w-n]
        have hG : D.gates[w-n]? = some G := List.getElem?_eq_getElem hj
        have he : n+(w-n) = w := by omega
        rcases hgate (w-n) G hG (by simpa [he]) (by simpa [he]) with hh | ⟨hl,hr⟩
        · simpa [he] using hh
        · rw [← he, val_gate D x _ _ hG, val_gate D y _ _ hG]
          congr 1
          · split_ifs with hlw
            · exact ih G.left (by omega) (by omega) (hl hlw)
            · rfl
          · split_ifs with hrw
            · exact ih G.right (by omega) (by omega) (hr hrw)
            · rfl
      · rw [val_beyond D x w (by omega), val_beyond D y w (by omega)]

def Reads (D : BinaryCircuit) (j w : ℕ) : Prop :=
  ∃ G, D.gates[j]? = some G ∧ (G.left = w ∨ G.right = w)

lemma branch_agree {n : ℕ} (D : BinaryCircuit) (x y : Fin n → Bool)
    (i : Fin n) (g k : ℕ)
    (hi : ∀ j, Reads D j i ↔ j = g)
    (hg : ∀ j, (Reads D j (n+g) ∧ g < j) ↔ j = k)
    (hin : ∀ q : Fin n, q ≠ i → x q = y q)
    (w : ℕ) (hw : w < n+k) (hwi : w ≠ i) (hwg : w ≠ n+g) :
    val D x w = val D y w := by
  refine agree D x y (fun z => z = i ∨ z = n+g) (n+k) ?_ ?_ w hw ?_
  · intro q hq
    exact hin q (fun he => hq (Or.inl (congrArg Fin.val he)))
  · intro j G hG hB hj
    right
    have avoid : ∀ z, (G.left = z ∨ G.right = z) → z < n+j →
        ¬ (z = i ∨ z = n+g) := by
      intro z hz hzlt he
      rcases he with he | he
      · have hjg := (hi j).mp ⟨G,hG,by simpa [he] using hz⟩
        exact hB (Or.inr (by omega))
      · have hjk := (hg j).mp ⟨⟨G,hG,by simpa [he] using hz⟩,by omega⟩
        omega
    exact ⟨avoid G.left (Or.inl rfl), avoid G.right (Or.inr rfl)⟩
  · exact not_or.mpr ⟨hwi,hwg⟩

lemma merge_agree {n : ℕ} (D : BinaryCircuit) (x y : Fin n → Bool)
    (v u : Fin n) (g h k : ℕ)
    (hv : ∀ j, Reads D j v ↔ j = g)
    (hu : ∀ j, Reads D j u ↔ j = h)
    (hg : ∀ j, (Reads D j (n+g) ∧ g < j) ↔ j = k)
    (hh : ∀ j, (Reads D j (n+h) ∧ h < j) ↔ j = k)
    (hin : ∀ q : Fin n, q ≠ v → q ≠ u → x q = y q)
    (hk : val D x (n+k) = val D y (n+k))
    (ho1 : D.output ≠ v) (ho2 : D.output ≠ u)
    (ho3 : D.output ≠ n+g) (ho4 : D.output ≠ n+h) :
    D.eval (List.ofFn x) = D.eval (List.ofFn y) := by
  change val D x D.output = val D y D.output
  refine agree D x y (fun z => z = v ∨ z = u ∨ z = n+g ∨ z = n+h)
    (D.output+1) ?_ ?_ D.output (by omega) ?_
  · intro q hq
    exact hin q (fun he => hq (Or.inl (congrArg Fin.val he)))
      (fun he => hq (Or.inr (Or.inl (congrArg Fin.val he))))
  · intro j G hG hB hj
    by_cases hjk : j = k
    · left; simpa [hjk] using hk
    · right
      have avoid : ∀ z, (G.left = z ∨ G.right = z) → z < n+j →
          ¬ (z = v ∨ z = u ∨ z = n+g ∨ z = n+h) := by
        intro z hz hzlt he
        rcases he with he | he | he | he
        · have hjg := (hv j).mp ⟨G,hG,by simpa [he] using hz⟩
          exact hB (Or.inr (Or.inr (Or.inl (by omega))))
        · have hjh := (hu j).mp ⟨G,hG,by simpa [he] using hz⟩
          exact hB (Or.inr (Or.inr (Or.inr (by omega))))
        · exact hjk ((hg j).mp ⟨⟨G,hG,by simpa [he] using hz⟩,by omega⟩)
        · exact hjk ((hh j).mp ⟨⟨G,hG,by simpa [he] using hz⟩,by omega⟩)
      exact ⟨avoid G.left (Or.inl rfl), avoid G.right (Or.inr rfl)⟩
  · exact not_or.mpr ⟨ho1,not_or.mpr ⟨ho2,not_or.mpr ⟨ho3,ho4⟩⟩⟩

lemma xor_funnel_comm (κ : Bool → Bool → Bool)
    (hκ : (κ false false = false ∧ κ false true = true ∧
        κ true false = true ∧ κ true true = false) ∨
      (κ false false = true ∧ κ false true = false ∧
        κ true false = false ∧ κ true true = true)) :
    ∀ a b, κ a b = κ b a := by
  intro a b
  rcases hκ with hκ | hκ <;> cases a <;> cases b <;> simp_all

lemma factor_xor_funnel (f κ : Bool → Bool → Bool) (φ ψ : Bool → Bool)
    (hκ : (κ false false = false ∧ κ false true = true ∧
        κ true false = true ∧ κ true true = false) ∨
      (κ false false = true ∧ κ false true = false ∧
        κ true false = false ∧ κ true true = true))
    (hfactor : ∀ a b a' b', κ (φ a) (ψ b) = κ (φ a') (ψ b') → f a b = f a' b') :
    f false false = f true true ∨
      (∀ a b, f a b = f (!a) b) ∨ (∀ a b, f a b = f a (!b)) := by
  by_cases hφ : φ false = φ true
  · right; left
    intro a b
    apply hfactor
    have ha : φ a = φ (!a) := by cases a <;> simp_all
    rw [ha]
  by_cases hψ : ψ false = ψ true
  · right; right
    intro a b
    apply hfactor
    have hb : ψ b = ψ (!b) := by cases b <;> simp_all
    rw [hb]
  left
  apply hfactor
  rcases hκ with hκ | hκ
  all_goals
    obtain ⟨h00,h01,h10,h11⟩ := hκ
    cases hφ0 : φ false <;> cases hφ1 : φ true <;>
      cases hψ0 : ψ false <;> cases hψ1 : ψ true <;> simp_all


end PEqualNP.Outside.L_meta_698_aux

open PEqualNP.Outside.L_meta_698_aux

theorem PEqualNP.Outside.L_meta_698 : ∀ (n : ℕ) (D : PEqualNP.MetaComplexity.BinaryCircuit) (v u : Fin n) (g h k : ℕ), v ≠ u → g ≠ h → (∀ j : ℕ, (∃ G : PEqualNP.MetaComplexity.BinaryGate, D.gates[j]? = some G ∧ (G.left = v.val ∨ G.right = v.val)) ↔ j = g) → (∀ j : ℕ, (∃ G : PEqualNP.MetaComplexity.BinaryGate, D.gates[j]? = some G ∧ (G.left = u.val ∨ G.right = u.val)) ↔ j = h) → (∃ G : PEqualNP.MetaComplexity.BinaryGate, D.gates[g]? = some G ∧ ¬ (G.left = v.val ∧ G.right = v.val)) → (∃ G : PEqualNP.MetaComplexity.BinaryGate, D.gates[h]? = some G ∧ ¬ (G.left = u.val ∧ G.right = u.val)) → (∀ j : ℕ, (∃ G : PEqualNP.MetaComplexity.BinaryGate, D.gates[j]? = some G ∧ (G.left = n + g ∨ G.right = n + g) ∧ g < j) ↔ j = k) → (∀ j : ℕ, (∃ G : PEqualNP.MetaComplexity.BinaryGate, D.gates[j]? = some G ∧ (G.left = n + h ∨ G.right = n + h) ∧ h < j) ↔ j = k) → (∃ G : PEqualNP.MetaComplexity.BinaryGate, D.gates[k]? = some G ∧ ((G.op false false = false ∧ G.op false true = true ∧ G.op true false = true ∧ G.op true true = false) ∨ (G.op false false = true ∧ G.op false true = false ∧ G.op true false = false ∧ G.op true true = true))) → D.output ≠ v.val → D.output ≠ u.val → D.output ≠ n + g → D.output ≠ n + h → ∀ (x : Fin n → Bool) (f : Bool → Bool → Bool), (∀ a b : Bool, f a b = D.eval (List.ofFn (Function.update (Function.update x v a) u b))) → (f false false = f true true ∨ (∀ a b : Bool, f a b = f (!a) b) ∨ (∀ a b : Bool, f a b = f a (!b))) := by

  classical
  intro n D v u g h k hvu hgh hvr hur _hgdata _hhdata hgr hhr hkdata ho1 ho2 ho3 ho4 x f hf
  have hv : ∀ j, Reads D j v ↔ j = g := by simpa [Reads] using hvr
  have hu : ∀ j, Reads D j u ↔ j = h := by simpa [Reads] using hur
  have hg : ∀ j, (Reads D j (n+g) ∧ g < j) ↔ j = k := by
    intro j
    constructor
    · rintro ⟨⟨G,hG,hr⟩,hgj⟩
      exact (hgr j).mp ⟨G,hG,hr,hgj⟩
    · intro hj
      obtain ⟨G,hG,hr,hgj⟩ := (hgr j).mpr hj
      exact ⟨⟨G,hG,hr⟩,hgj⟩
  have hh : ∀ j, (Reads D j (n+h) ∧ h < j) ↔ j = k := by
    intro j
    constructor
    · rintro ⟨⟨G,hG,hr⟩,hhj⟩
      exact (hhr j).mp ⟨G,hG,hr,hhj⟩
    · intro hj
      obtain ⟨G,hG,hr,hhj⟩ := (hhr j).mpr hj
      exact ⟨⟨G,hG,hr⟩,hhj⟩
  obtain ⟨Gk,hGk,hκ⟩ := hkdata
  obtain ⟨⟨Gkg,hGkg,hgkr⟩,hgk⟩ := (hg k).mpr rfl
  have eGg : Gkg = Gk := Option.some.inj (hGkg.symm.trans hGk)
  subst Gkg
  obtain ⟨⟨Gkh,hGkh,hhkr⟩,hhk⟩ := (hh k).mpr rfl
  have eGh : Gkh = Gk := Option.some.inj (hGkh.symm.trans hGk)
  subst Gkh
  have hpair : (Gk.left = n+g ∧ Gk.right = n+h) ∨
      (Gk.left = n+h ∧ Gk.right = n+g) := by
    rcases hgkr with hgkr | hgkr <;> rcases hhkr with hhkr | hhkr <;> omega
  let X : Bool → Bool → Fin n → Bool := fun a b => Function.update (Function.update x v a) u b
  let φ : Bool → Bool := fun a => val D (X a false) (n+g)
  let ψ : Bool → Bool := fun b => val D (X false b) (n+h)
  have hφ : ∀ a b, val D (X a b) (n+g) = φ a := by
    intro a b
    apply branch_agree D (X a b) (X a false) u h k hu hh
    · intro q hqu
      simp [X,Function.update_of_ne hqu]
    · omega
    · have := u.isLt; omega
    · omega
  have hψ : ∀ a b, val D (X a b) (n+h) = ψ b := by
    intro a b
    apply branch_agree D (X a b) (X false b) v g k hv hg
    · intro q hqv
      by_cases hqu : q = u
      · simp [X,hqu]
      · simp [X,Function.update_of_ne hqu,Function.update_of_ne hqv]
    · omega
    · have := v.isLt; omega
    · omega
  have hkval : ∀ a b, val D (X a b) (n+k) = Gk.op (φ a) (ψ b) := by
    intro a b
    rw [val_gate D (X a b) k Gk hGk]
    rcases hpair with ⟨hl,hr⟩ | ⟨hl,hr⟩
    · rw [hl,hr,if_pos (by omega),if_pos (by omega),hφ,hψ]
    · rw [hl,hr,if_pos (by omega),if_pos (by omega),hφ,hψ]
      exact xor_funnel_comm Gk.op hκ _ _
  apply factor_xor_funnel f Gk.op φ ψ hκ
  intro a b a' b' he
  rw [hf a b,hf a' b']
  apply merge_agree D (X a b) (X a' b') v u g h k hv hu hg hh
  · intro q hqv hqu
    simp [X,Function.update_of_ne hqu,Function.update_of_ne hqv]
  · rw [hkval,hkval,he]
  · exact ho1
  · exact ho2
  · exact ho3
  · exact ho4
