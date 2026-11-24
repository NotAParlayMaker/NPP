import PEqualNP.Defs
import PEqualNP.MetaComplexity.Helpers.LowerPart
import PEqualNP.MetaComplexity.Helpers.LowerPart2

namespace PEqualNP.Outside.L_meta_4712_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.MetaComplexity.FoldProg
open PEqualNP.MetaComplexity.LowerPart
open PEqualNP.TopForm PEqualNP.CleanedNonEdge
open PEqualNP.SplitCount (unitInput)
open PEqualNP.EdgeOwnership (gateVal pairInput)

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
variable {C : Circuit} {g : ℕ}

def Smaller (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) : Prop :=
  ∃ D : Circuit, IsAO2 n D ∧ D.size < C.size ∧ circuitFun n D = graphFun G ∅

theorem singleton_value (H : OneDirty G C g) (c : Fin 2) (w : Fin n)
    (single : ∀ y, wireVal n C (opnd C g c) (unitInput y) = true ↔ y = w)
    (x : Fin n → Bool) : wireVal n C (opnd C g c) x = x w := by
  have hi : wireVal n C (opnd C g c) x = true ↔ x w = true := by
    rw [opnd_val H c x]
    constructor
    · rintro ⟨y, hy, hu⟩
      rwa [(single y).1 hu] at hy
    · intro h
      exact ⟨w, h, (single w).2 rfl⟩
  exact Bool.eq_iff_iff.mpr hi

theorem singleton_computed_shorter (H : OneDirty G C g) (c : Fin 2) (w : Fin n)
    (single : ∀ y, wireVal n C (opnd C g c) (unitInput y) = true ↔ y = w)
    (computed : n ≤ opnd C g c) : Smaller G C := by
  let k := opnd C g c - n
  have e : n + k = opnd C g c := by dsimp [k]; omega
  have back := opnd_lt C H.ao g H.hg c
  have hg := H.hg
  have hw := w.isLt
  have hk : k < C.gates.length := by omega
  apply dup_lt H k hk w.val (by omega)
  intro x
  change wireVal n C (n + k) x = wireVal n C w.val x
  rw [e, singleton_value H c w single, wireVal_lt C w.val w.isLt]

theorem exists_bad (H : OneDirty G C g) (c : Fin 2) (w : Fin n)
    (single : ∀ y, wireVal n C (opnd C g c) (unitInput y) = true ↔ y = w) :
    ∃ a, wireVal n C (opnd C g (1-c)) (unitInput a) = true ∧ ¬ G.Adj w a := by
  classical
  by_contra! noBad
  apply H.dirty
  intro x hx
  obtain ⟨hw, ha⟩ := (val_and' C H.ao g H.hg H.gand x c).1 hx
  rw [singleton_value H c w single] at hw
  obtain ⟨a, hax, ham⟩ := (opnd_val H (1-c) x).1 ha
  exact (graphFun_empty G x).2 ⟨w, a, noBad a ham, hw, hax⟩

theorem partner_not_singleton (H : OneDirty G C g) (c : Fin 2) (w : Fin n)
    (single : ∀ y, wireVal n C (opnd C g c) (unitInput y) = true ↔ y = w)
    (k : ℕ) (hk : k < C.gates.length) (hand : (gateAt C k).op = .and) :
    ¬ PZ C g k w := by
  intro hp
  apply H.dirty
  intro x hx
  have hw := ((val_and' C H.ao g H.hg H.gand x c).1 hx).1
  rw [singleton_value H c w single] at hw
  exact pz_F H k hk hand w hp x hx hw

theorem partner_triangle (H : OneDirty G C g) (c : Fin 2) (w : Fin n)
    (single : ∀ y, wireVal n C (opnd C g c) (unitInput y) = true ↔ y = w)
    (k : ℕ) (hk : k < C.gates.length) (hand : (gateAt C k).op = .and)
    (z : Fin n) (hz : PZ C g k z) (a : Fin n)
    (ha : wireVal n C (opnd C g (1-c)) (unitInput a) = true) :
    G.Adj w a ∨ G.Adj w z ∨ G.Adj a z := by
  let x : Fin n → Bool := fun y => decide (y = w ∨ y = a ∨ y = z)
  have hgx : gateVal n C g x = true := by
    apply (val_and' C H.ao g H.hg H.gand x c).2
    constructor
    · rw [singleton_value H c w single]
      simp [x]
    · exact (opnd_val H (1-c) x).2 ⟨a, by simp [x], ha⟩
  have hf := pz_F H k hk hand z hz x hgx (by simp [x])
  obtain ⟨u, v, huv, hu, hv⟩ := (graphFun_empty G x).1 hf
  simp only [x, decide_eq_true_eq] at hu hv
  rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl
  · exact False.elim (G.loopless.irrefl _ huv)
  · exact Or.inl huv
  · exact Or.inr (Or.inl huv)
  · exact Or.inl huv.symm
  · exact False.elim (G.loopless.irrefl _ huv)
  · exact Or.inr (Or.inr huv)
  · exact Or.inr (Or.inl huv.symm)
  · exact Or.inr (Or.inr huv.symm)
  · exact False.elim (G.loopless.irrefl _ huv)

theorem partner_opposite_adj (H : OneDirty G C g) (s : Fin n → Bool)
    (bip : ∀ u v, G.Adj u v → s u ≠ s v)
    (c : Fin 2) (w : Fin n)
    (single : ∀ y, wireVal n C (opnd C g c) (unitInput y) = true ↔ y = w)
    (opposite : ∀ y, wireVal n C (opnd C g (1-c)) (unitInput y) = true → s y ≠ s w)
    (k : ℕ) (hk : k < C.gates.length) (hand : (gateAt C k).op = .and)
    (z : Fin n) (hz : PZ C g k z) (hzw : s z ≠ s w) : G.Adj w z := by
  obtain ⟨a, ha, bad⟩ := exists_bad H c w single
  have haw := opposite a ha
  have same : s a = s z := by
    have hb : ∀ p q r : Bool, p ≠ r → q ≠ r → p = q := by decide
    exact hb (s a) (s z) (s w) haw hzw
  rcases partner_triangle H c w single k hk hand z hz a ha with h | h | h
  · exact False.elim (bad h)
  · exact h
  · exact False.elim (bip a z h same)

end PEqualNP.Outside.L_meta_4712_aux


namespace PEqualNP.Outside.L_meta_4712_aux.Partner

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.MetaComplexity.FoldProg
open PEqualNP.MetaComplexity.LowerPart
open PEqualNP.TopForm PEqualNP.CleanedNonEdge
open PEqualNP.SplitCount (unitInput)
open PEqualNP.EdgeOwnership (gateVal pairInput)

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
variable {C : Circuit} {g : ℕ}

lemma same_color_of_adj (s : Fin n → Bool)
    (bip : ∀ u v, G.Adj u v → s u ≠ s v)
    {a b z : Fin n} (ha : G.Adj a z) (hb : G.Adj b z) : s a = s b := by
  have h1 := bip a z ha
  have h2 := bip b z hb
  cases hsa : s a <;> cases hsb : s b <;> cases hsz : s z <;> simp_all

lemma pure_support_nonempty (H : OneDirty G C g) (k : ℕ)
    (hk : k < C.gates.length) (ho : (gateAt C k).op = .and) (c : Fin 2)
    (pure : ¬ OrReaches n C (opnd C k c) g) :
    ∃ z, wireVal n C (opnd C k c) (unitInput z) = true := by
  have hl := opnd_lt C H.ao k hk c
  have hone := ones_val C H.ao (opnd C k c) (by omega)
  obtain ⟨z, _, hz⟩ := (pure_val H k hk ho c pure (fun _ => true)).1 hone
  exact ⟨z, hz⟩

lemma and_support_homogeneous (H : OneDirty G C g) (s : Fin n → Bool)
    (bip : ∀ u v, G.Adj u v → s u ≠ s v)
    (k : ℕ) (hk : k < C.gates.length) (ho : (gateAt C k).op = .and)
    (hkg : k ≠ g) (c : Fin 2) {a b z : Fin n}
    (ha : wireVal n C (opnd C k c) (unitInput a) = true)
    (hb : wireVal n C (opnd C k c) (unitInput b) = true)
    (hz : wireVal n C (opnd C k (1-c)) (unitInput z) = true) :
    s a = s b :=
  same_color_of_adj s bip
    (and_pair' H k hk ho hkg c a z ha hz)
    (and_pair' H k hk ho hkg c b z hb hz)

lemma and_mixed_other_empty (H : OneDirty G C g) (s : Fin n → Bool)
    (bip : ∀ u v, G.Adj u v → s u ≠ s v)
    (k : ℕ) (hk : k < C.gates.length) (ho : (gateAt C k).op = .and)
    (hkg : k ≠ g) (c : Fin 2) {a b : Fin n}
    (ha : wireVal n C (opnd C k c) (unitInput a) = true)
    (hb : wireVal n C (opnd C k c) (unitInput b) = true)
    (hab : s a ≠ s b) :
    ∀ z, wireVal n C (opnd C k (1-c)) (unitInput z) = false := by
  intro z
  apply Bool.eq_false_iff.mpr
  intro hz
  exact hab (and_support_homogeneous H s bip k hk ho hkg c ha hb hz)

lemma reaching_support_homogeneous (H : OneDirty G C g) (s : Fin n → Bool)
    (bip : ∀ u v, G.Adj u v → s u ≠ s v)
    (u : ℕ) (hu : u < n + C.gates.length) (hr : OrReaches n C u g)
    {a b : Fin n}
    (ha : wireVal n C u (unitInput a) = true)
    (hb : wireVal n C u (unitInput b) = true) : s a = s b := by
  rcases srcOf_cases (n := n) u with ⟨i, rfl⟩ | ⟨k, rfl⟩
  · exact False.elim (reach_input C i.val g i.isLt hr)
  · have hk : k < C.gates.length := by omega
    have low : Low G C (n+k) := by
      intro hlow
      apply H.dirty
      intro x hx
      exact hlow x ((reach_le C H.ao g _ hu hr).2 x hx)
    obtain ⟨T, hT, hTo, c, hTk⟩ := above_and H k hk low
    have hcl := opnd_lt C H.ao T hT c
    have hcg : OrReaches n C (opnd C T c) g :=
      reach_trans C H.ao k g hk hr _ (by omega) hTk
    have otherPure := not_both' H T hT hTo c hcg
    obtain ⟨z, hz⟩ := pure_support_nonempty H T hT hTo (1-c) otherPure
    have hTg : T ≠ g := pz_ne H T z ((pz_iff C g T z).2 ⟨c, hcg, hz⟩)
    have ha' : wireVal n C (opnd C T c) (unitInput a) = true :=
      (reach_le C H.ao k _ (by omega) hTk).2 _ ha
    have hb' : wireVal n C (opnd C T c) (unitInput b) = true :=
      (reach_le C H.ao k _ (by omega) hTk).2 _ hb
    exact and_support_homogeneous H s bip T hT hTo hTg c ha' hb' hz

lemma mixed_not_reaching (H : OneDirty G C g) (s : Fin n → Bool)
    (bip : ∀ u v, G.Adj u v → s u ≠ s v)
    (u : ℕ) (hu : u < n + C.gates.length) {a b : Fin n}
    (ha : wireVal n C u (unitInput a) = true)
    (hb : wireVal n C u (unitInput b) = true) (hab : s a ≠ s b) :
    ¬ OrReaches n C u g := by
  intro hr
  exact hab (reaching_support_homogeneous H s bip u hu hr ha hb)

lemma empty_support_shorter (H : OneDirty G C g) (k : ℕ)
    (hk : k < C.gates.length) (hkg : k ≠ g)
    (hlow : Low G C (n+k))
    (hempty : ∀ y, wireVal n C (n+k) (unitInput y) = false) :
    ∃ D : Circuit, IsAO2 n D ∧ D.size < C.size ∧ circuitFun n D = graphFun G ∅ := by
  have hbound : n+k < n+C.gates.length := by omega
  have hone := ones_val C H.ao (n+k) hbound
  have hreach : OrReaches n C (n+k) g := by
    rcases (val_low H (n+k) hbound hlow (fun _ => true)).1 hone with
      ⟨y, _, hy⟩ | ⟨hr, _⟩
    · rw [hempty y] at hy
      cases hy
    · exact hr
  have hle := (reach_le C H.ao g (n+k) hbound hreach).1
  apply dup_lt H k hk (n+g) (by omega)
  intro x
  apply Bool.eq_iff_iff.mpr
  change wireVal n C (n+k) x = true ↔ gateVal n C g x = true
  rw [val_low H (n+k) hbound hlow x]
  simp [hempty, hreach]

lemma low_support_nonempty_of_not_smaller (H : OneDirty G C g)
    (hmin : ¬ ∃ D : Circuit, IsAO2 n D ∧ D.size < C.size ∧
      circuitFun n D = graphFun G ∅)
    (u : ℕ) (hu : u < n+C.gates.length) (hlow : Low G C u)
    (hne : u ≠ n+g) :
    ∃ y, wireVal n C u (unitInput y) = true := by
  rcases srcOf_cases (n := n) u with ⟨i, rfl⟩ | ⟨k, rfl⟩
  · refine ⟨i, ?_⟩
    rw [wireVal_lt C i.val i.isLt]
    simp [unitInput]
  · have hk : k < C.gates.length := by omega
    have hkg : k ≠ g := by omega
    by_contra! hempty
    apply hmin
    apply empty_support_shorter H k hk hkg hlow
    intro y
    exact Bool.eq_false_iff.mpr (hempty y)

lemma pair_other_color (s : Fin n → Bool)
    (bip : ∀ u v, G.Adj u v → s u ≠ s v)
    {p q w z : Fin n} (hpq : G.Adj p q)
    (hw : pairInput p q w = true) (hz : pairInput p q z = true)
    (hzw : z ≠ w) : s z ≠ s w := by
  simp only [pairInput, decide_eq_true_eq] at hw hz
  rcases hw with rfl | rfl <;> rcases hz with rfl | rfl
  · exact False.elim (hzw rfl)
  · exact bip _ _ hpq.symm
  · exact bip _ _ hpq
  · exact False.elim (hzw rfl)

end PEqualNP.Outside.L_meta_4712_aux.Partner


namespace PEqualNP.Outside.L_meta_4712_aux.Transform

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.MetaComplexity.FoldProg
open PEqualNP.MetaComplexity.LowerPart
open PEqualNP.TopForm PEqualNP.CleanedNonEdge
open PEqualNP.SplitCount (unitInput)
open PEqualNP.EdgeOwnership (gateVal pairInput)

variable {n : ℕ}

def unitPart (C : Circuit) (u : ℕ) (x : Fin n → Bool) : Bool :=
  (List.ofFn fun y : Fin n => x y && wireVal n C u (unitInput y)).any id

def pointPart (C : Circuit) (s : Fin n → Bool) (w : Fin n) (u : ℕ)
    (x : Fin n → Bool) : Bool :=
  (List.ofFn fun y : Fin n => x y && wireVal n C u (unitInput y) && decide (s y ≠ s w)).any id

def pt (C : Circuit) (s : Fin n → Bool) (w : Fin n) (u : ℕ) : Bool :=
  pointPart C s w u (fun _ => true)

def reaches (C : Circuit) (g u : ℕ) : Bool :=
  decide (n ≤ u ∧ g ∈ (orSets n C).getD (u-n) [])

def lowFlag (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (k : ℕ) : Bool :=
  decide (¬ ∀ x : Fin n → Bool, wireVal n C (n+k) x = true → graphFun G ∅ x = true)

def lowVal (C : Circuit) (s : Fin n → Bool) (w : Fin n) (g u : ℕ)
    (x : Fin n → Bool) : Bool :=
  if pt C s w u then pointPart C s w u x
  else unitPart C u x || (reaches (n := n) C g u && x w)

def route (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : Fin n → Bool) (w : Fin n) (g k : ℕ) (c : Fin 2) : Src n ℕ :=
  let u := opnd C k c
  if isA (gateAt C k).op then
    if u = n+g then
      if pt C s w (opnd C k (1-c)) then some (Sum.inl w) else none
    else srcOf n u
  else if lowFlag G C k then
    if pt C s w (n+k) then
      if pt C s w u then srcOf n u else none
    else if u = n+g then some (Sum.inl w) else srcOf n u
  else srcOf n u

def values (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : Fin n → Bool) (w : Fin n) (g : ℕ) (x : Fin n → Bool) (k : ℕ) : Bool :=
  if lowFlag G C k then lowVal C s w g (n+k) x else gateVal n C k x

theorem unitPart_iff (C : Circuit) (u : ℕ) (x : Fin n → Bool) :
    unitPart C u x = true ↔ ∃ y, x y = true ∧ wireVal n C u (unitInput y) = true := by
  simp [unitPart, List.any_eq_true]

theorem pointPart_iff (C : Circuit) (s : Fin n → Bool) (w : Fin n) (u : ℕ)
    (x : Fin n → Bool) :
    pointPart C s w u x = true ↔
      ∃ y, x y = true ∧ wireVal n C u (unitInput y) = true ∧ s y ≠ s w := by
  simp [pointPart, List.any_eq_true, and_assoc]

theorem pt_iff (C : Circuit) (s : Fin n → Bool) (w : Fin n) (u : ℕ) :
    pt C s w u = true ↔ ∃ y, wireVal n C u (unitInput y) = true ∧ s y ≠ s w := by
  simp [pt, pointPart_iff]

theorem reaches_iff (C : Circuit) (g u : ℕ) :
    reaches (n := n) C g u = true ↔ OrReaches n C u g := by
  change decide (n ≤ u ∧ g ∈ (orSets n C).getD (u-n) []) = true ↔
    n ≤ u ∧ g ∈ (orSets n C).getD (u-n) []
  simp only [decide_eq_true_eq]

theorem lowFlag_iff (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (k : ℕ) :
    lowFlag G C k = true ↔ Low G C (n+k) := by
  change decide (¬ ∀ x : Fin n → Bool, wireVal n C (n+k) x = true → graphFun G ∅ x = true) = true ↔
    ¬ ∀ x : Fin n → Bool, wireVal n C (n+k) x = true → graphFun G ∅ x = true
  simp only [decide_eq_true_eq]

theorem lowVal_iff (C : Circuit) (s : Fin n → Bool) (w : Fin n) (g u : ℕ)
    (x : Fin n → Bool) : lowVal C s w g u x = true ↔
      (if pt C s w u then
        ∃ y, x y = true ∧ wireVal n C u (unitInput y) = true ∧ s y ≠ s w
       else (∃ y, x y = true ∧ wireVal n C u (unitInput y) = true) ∨
         (OrReaches n C u g ∧ x w = true)) := by
  simp [lowVal, pointPart_iff, unitPart_iff, reaches_iff]

theorem bool_ext {a b : Bool} (h : a = true ↔ b = true) : a = b := by
  cases a <;> cases b <;> simp_all

theorem unitPart_input (C : Circuit) (i : Fin n) (x : Fin n → Bool) :
    unitPart C i.val x = x i := by
  apply bool_ext
  rw [unitPart_iff]
  simp [wireVal_lt C i.val i.isLt, unitInput]

theorem pointPart_input (C : Circuit) (s : Fin n → Bool) (w i : Fin n)
    (x : Fin n → Bool) :
    pointPart C s w i.val x = (x i && decide (s i ≠ s w)) := by
  apply bool_ext
  rw [pointPart_iff]
  simp [wireVal_lt C i.val i.isLt, unitInput]

theorem pt_input (C : Circuit) (s : Fin n → Bool) (w i : Fin n) :
    pt C s w i.val = decide (s i ≠ s w) := by
  simp [pt, pointPart_input]

theorem reaches_input (C : Circuit) (g : ℕ) (i : Fin n) :
    reaches (n := n) C g i.val = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  exact reach_input C i.val g i.isLt ((reaches_iff C g i.val).1 h)

theorem lowVal_input (C : Circuit) (s : Fin n → Bool) (w i : Fin n) (g : ℕ)
    (x : Fin n → Bool) : lowVal C s w g i.val x = x i := by
  simp only [lowVal, pt_input, pointPart_input, unitPart_input, reaches_input,
    Bool.false_and, Bool.or_false]
  by_cases h : s i ≠ s w <;> simp [h]

theorem srcAt_values_low (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : Fin n → Bool) (w : Fin n) (g u : ℕ) (x : Fin n → Bool)
    (hl : Low G C u) :
    srcAt x (values G C s w g x) (srcOf n u) = lowVal C s w g u x := by
  rcases srcOf_cases (n := n) u with ⟨i, rfl⟩ | ⟨k, rfl⟩
  · rw [srcOf_input]
    change x i = lowVal C s w g i.val x
    exact (lowVal_input C s w i g x).symm
  · rw [srcOf_gate]
    change values G C s w g x k = lowVal C s w g (n+k) x
    simp [values, (lowFlag_iff G C k).2 hl]

theorem route_and_val {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} {g : ℕ} (H : OneDirty G C g)
    (s : Fin n → Bool) (w : Fin n) (k : ℕ) (hk : k < C.gates.length)
    (hand : (gateAt C k).op = .and) (c : Fin 2) (x : Fin n → Bool) :
    srcAt x (values G C s w g x) (route G C s w g k c) =
      if opnd C k c = n+g then
        (if pt C s w (opnd C k (1-c)) then x w else false)
      else lowVal C s w g (opnd C k c) x := by
  simp only [route, hand, isA, ite_true]
  by_cases he : opnd C k c = n+g
  · simp only [he, ite_true]
    cases pt C s w (opnd C k (1-c)) <;> rfl
  · simp only [he, ite_false]
    exact srcAt_values_low G C s w g _ x (low_opnd H k hk c (Or.inr hand))

theorem pointPart_le_pt (C : Circuit) (s : Fin n → Bool) (w : Fin n) (u : ℕ)
    (x : Fin n → Bool) (h : pointPart C s w u x = true) : pt C s w u = true := by
  obtain ⟨y, _, hy, hp⟩ := (pointPart_iff C s w u x).1 h
  exact (pt_iff C s w u).2 ⟨y, hy, hp⟩

theorem pointPart_of_not_pt (C : Circuit) (s : Fin n → Bool) (w : Fin n) (u : ℕ)
    (h : pt C s w u = false) (x : Fin n → Bool) : pointPart C s w u x = false := by
  apply Bool.eq_false_iff.mpr
  intro hp
  rw [pointPart_le_pt C s w u x hp] at h
  contradiction

theorem select_lowVal (C : Circuit) (s : Fin n → Bool) (w : Fin n) (g u : ℕ)
    (x : Fin n → Bool) :
    (if pt C s w u then lowVal C s w g u x else false) = pointPart C s w u x := by
  cases h : pt C s w u
  · simp [h, pointPart_of_not_pt C s w u h x]
  · simp [h, lowVal]

theorem unitPart_or (C : Circuit) (hC : IsAO2 n C) (k : ℕ) (hk : k < C.gates.length)
    (ho : (gateAt C k).op = .or) (x : Fin n → Bool) :
    unitPart C (n+k) x = (unitPart C (opnd C k 0) x || unitPart C (opnd C k 1) x) := by
  apply bool_ext
  rw [unitPart_iff, Bool.or_eq_true, unitPart_iff, unitPart_iff]
  have hv : ∀ y : Fin n, wireVal n C (n+k) (unitInput y) = true ↔
      wireVal n C (opnd C k 0) (unitInput y) = true ∨
      wireVal n C (opnd C k 1) (unitInput y) = true :=
    fun y => val_or C hC k hk ho (unitInput y)
  simp_rw [hv, and_or_left, exists_or]

theorem pointPart_or (C : Circuit) (hC : IsAO2 n C) (s : Fin n → Bool) (w : Fin n)
    (k : ℕ) (hk : k < C.gates.length) (ho : (gateAt C k).op = .or) (x : Fin n → Bool) :
    pointPart C s w (n+k) x =
      (pointPart C s w (opnd C k 0) x || pointPart C s w (opnd C k 1) x) := by
  apply bool_ext
  rw [pointPart_iff, Bool.or_eq_true, pointPart_iff, pointPart_iff]
  have hv : ∀ y : Fin n, wireVal n C (n+k) (unitInput y) = true ↔
      wireVal n C (opnd C k 0) (unitInput y) = true ∨
      wireVal n C (opnd C k 1) (unitInput y) = true :=
    fun y => val_or C hC k hk ho (unitInput y)
  simp_rw [hv, or_and_right, and_or_left, exists_or]

theorem pt_or (C : Circuit) (hC : IsAO2 n C) (s : Fin n → Bool) (w : Fin n)
    (k : ℕ) (hk : k < C.gates.length) (ho : (gateAt C k).op = .or) :
    pt C s w (n+k) = (pt C s w (opnd C k 0) || pt C s w (opnd C k 1)) :=
  pointPart_or C hC s w k hk ho (fun _ => true)

theorem reaches_or (C : Circuit) (hC : IsAO2 n C) (g k : ℕ) (hk : k < C.gates.length)
    (ho : (gateAt C k).op = .or) (hne : k ≠ g) :
    reaches (n := n) C g (n+k) =
      (reaches (n := n) C g (opnd C k 0) || reaches (n := n) C g (opnd C k 1)) := by
  apply bool_ext
  rw [reaches_iff, Bool.or_eq_true, reaches_iff, reaches_iff, reach_gate C hC k g hk]
  constructor
  · rintro (e | ⟨_, b, hb⟩)
    · exact False.elim (hne e.symm)
    · fin_cases b
      · exact Or.inl hb
      · exact Or.inr hb
  · rintro (h | h)
    · exact Or.inr ⟨ho, 0, h⟩
    · exact Or.inr ⟨ho, 1, h⟩

theorem dirty_parts_zero (C : Circuit) (s : Fin n → Bool) (w : Fin n) (g : ℕ)
    (hu : ∀ y : Fin n, gateVal n C g (unitInput y) = false) :
    pt C s w (n+g) = false ∧ ∀ x : Fin n → Bool, unitPart C (n+g) x = false := by
  have hs : ∀ y : Fin n, wireVal n C (n+g) (unitInput y) = false := hu
  constructor
  · apply Bool.eq_false_iff.mpr
    rintro h
    obtain ⟨y, hy, _⟩ := (pt_iff C s w (n+g)).1 h
    rw [hs] at hy
    contradiction
  · intro x
    apply Bool.eq_false_iff.mpr
    rintro h
    obtain ⟨y, _, hy⟩ := (unitPart_iff C (n+g) x).1 h
    rw [hs] at hy
    contradiction

theorem lowVal_dirty {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} {g : ℕ} (H : OneDirty G C g) (s : Fin n → Bool) (w : Fin n)
    (hu : ∀ y : Fin n, gateVal n C g (unitInput y) = false) (x : Fin n → Bool) :
    lowVal C s w g (n+g) x = x w := by
  obtain ⟨hp, hv⟩ := dirty_parts_zero C s w g hu
  have hr : reaches (n := n) C g (n+g) = true :=
    (reaches_iff C g (n+g)).2 (reach_self C H.ao g H.hg)
  simp [lowVal, hp, hv, hr]

theorem route_or_low_val {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} {g : ℕ} (H : OneDirty G C g) (s : Fin n → Bool) (w : Fin n)
    (hu : ∀ y : Fin n, gateVal n C g (unitInput y) = false)
    (k : ℕ) (hk : k < C.gates.length) (ho : (gateAt C k).op = .or)
    (hl : Low G C (n+k)) (c : Fin 2) (x : Fin n → Bool) :
    srcAt x (values G C s w g x) (route G C s w g k c) =
      if pt C s w (n+k) then
        (if pt C s w (opnd C k c) then lowVal C s w g (opnd C k c) x else false)
      else lowVal C s w g (opnd C k c) x := by
  have hp := low_opnd H k hk c (Or.inl hl)
  simp only [route, ho, isA, Bool.false_eq_true, ite_false, (lowFlag_iff G C k).2 hl, ite_true]
  cases h : pt C s w (n+k)
  · simp only [h, Bool.false_eq_true, ite_false]
    by_cases he : opnd C k c = n+g
    · simp only [he, ite_true]
      change x w = lowVal C s w g (n+g) x
      exact (lowVal_dirty H s w hu x).symm
    · simp only [he, ite_false]
      exact srcAt_values_low G C s w g _ x hp
  · simp only [h, ite_true]
    cases hchild : pt C s w (opnd C k c)
    · rfl
    · exact srcAt_values_low G C s w g _ x hp

theorem low_or_equation {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} {g : ℕ} (H : OneDirty G C g) (s : Fin n → Bool) (w : Fin n)
    (hu : ∀ y : Fin n, gateVal n C g (unitInput y) = false)
    (k : ℕ) (hk : k < C.gates.length) (ho : (gateAt C k).op = .or)
    (hl : Low G C (n+k)) (x : Fin n → Bool) :
    opv (isA (gateAt C k).op)
      (srcAt x (values G C s w g x) (route G C s w g k 0))
      (srcAt x (values G C s w g x) (route G C s w g k 1)) =
      lowVal C s w g (n+k) x := by
  have hne : k ≠ g := by
    rintro rfl
    rw [H.gand] at ho
    contradiction
  rw [route_or_low_val H s w hu k hk ho hl 0 x,
    route_or_low_val H s w hu k hk ho hl 1 x]
  simp only [ho, isA, opv]
  cases hp : pt C s w (n+k)
  · have hc : pt C s w (opnd C k 0) = false ∧ pt C s w (opnd C k 1) = false := by
      rw [pt_or C H.ao s w k hk ho] at hp
      simpa using hp
    simp only [hp, Bool.false_eq_true, ite_false, lowVal, hc.1, hc.2]
    rw [unitPart_or C H.ao k hk ho x, reaches_or C H.ao g k hk ho hne]
    cases unitPart C (opnd C k 0) x <;> cases unitPart C (opnd C k 1) x <;>
      cases reaches (n := n) C g (opnd C k 0) <;> cases reaches (n := n) C g (opnd C k 1) <;>
      cases x w <;> rfl
  · simp only [hp, ite_true]
    rw [select_lowVal, select_lowVal]
    simp only [lowVal, hp, ite_true]
    exact (pointPart_or C H.ao s w k hk ho x).symm

theorem color_of_not_pt (C : Circuit) (s : Fin n → Bool) (w : Fin n) (u : ℕ)
    (hp : pt C s w u = false) (y : Fin n) (hy : wireVal n C u (unitInput y) = true) :
    s y = s w := by
  by_contra h
  have ht := (pt_iff C s w u).2 ⟨y, hy, h⟩
  rw [hp] at ht
  contradiction

theorem lowVal_cases (C : Circuit) (s : Fin n → Bool) (w : Fin n) (g u : ℕ)
    (x : Fin n → Bool) (h : lowVal C s w g u x = true) :
    (∃ y, x y = true ∧ wireVal n C u (unitInput y) = true) ∨
      (pt C s w u = false ∧ OrReaches n C u g ∧ x w = true) := by
  rw [lowVal_iff] at h
  cases hp : pt C s w u
  · simp only [hp, Bool.false_eq_true, ite_false] at h
    rcases h with h | ⟨hr, hw⟩
    · exact Or.inl h
    · exact Or.inr ⟨rfl, hr, hw⟩
  · simp only [hp, ite_true] at h
    obtain ⟨y, hy, hs, _⟩ := h
    exact Or.inl ⟨y, hy, hs⟩

theorem lowVal_point (C : Circuit) (s : Fin n → Bool) (w : Fin n) (g u : ℕ)
    (x : Fin n → Bool) (hp : pt C s w u = true) (h : lowVal C s w g u x = true) :
    ∃ y, x y = true ∧ wireVal n C u (unitInput y) = true ∧ s y ≠ s w := by
  rw [lowVal_iff] at h
  simpa only [hp, ite_true] using h

theorem srcAt_values_below (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : Fin n → Bool) (w : Fin n) (g u : ℕ) (x : Fin n → Bool)
    (hb : ∀ y, wireVal n C u y = true → graphFun G ∅ y = true) :
    srcAt x (values G C s w g x) (srcOf n u) = wireVal n C u x := by
  rcases srcOf_cases (n := n) u with ⟨i, rfl⟩ | ⟨k, rfl⟩
  · rw [srcOf_input, wireVal_lt C i.val i.isLt]
    rfl
  · rw [srcOf_gate]
    have hl : lowFlag G C k = false := by
      apply Bool.eq_false_iff.mpr
      intro h
      exact ((lowFlag_iff G C k).1 h) hb
    change values G C s w g x k = gateVal n C k x
    simp [values, hl]

theorem route_or_below_val {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} {g : ℕ} (H : OneDirty G C g) (s : Fin n → Bool) (w : Fin n)
    (k : ℕ) (hk : k < C.gates.length) (ho : (gateAt C k).op = .or)
    (hb : BelowF G C k) (c : Fin 2) (x : Fin n → Bool) :
    srcAt x (values G C s w g x) (route G C s w g k c) =
      wireVal n C (opnd C k c) x := by
  have hl : lowFlag G C k = false := by
    apply Bool.eq_false_iff.mpr
    intro h
    exact ((lowFlag_iff G C k).1 h) hb
  simp only [route, ho, isA, Bool.false_eq_true, ite_false, hl]
  exact srcAt_values_below G C s w g _ x (below_or H.ao k hk ho hb c)

theorem high_or_equation {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} {g : ℕ} (H : OneDirty G C g) (s : Fin n → Bool) (w : Fin n)
    (k : ℕ) (hk : k < C.gates.length) (ho : (gateAt C k).op = .or)
    (hb : BelowF G C k) (x : Fin n → Bool) :
    opv (isA (gateAt C k).op)
      (srcAt x (values G C s w g x) (route G C s w g k 0))
      (srcAt x (values G C s w g x) (route G C s w g k 1)) =
      gateVal n C k x := by
  rw [route_or_below_val H s w k hk ho hb 0 x,
    route_or_below_val H s w k hk ho hb 1 x]
  exact (gate_eq C H.ao k hk x).symm

end PEqualNP.Outside.L_meta_4712_aux.Transform

namespace PEqualNP.Outside.L_meta_4712_aux.Transform.Edge

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.MetaComplexity.FoldProg
open PEqualNP.MetaComplexity.LowerPart
open PEqualNP.TopForm PEqualNP.CleanedNonEdge
open PEqualNP.SplitCount (unitInput)
open PEqualNP.EdgeOwnership (gateVal pairInput)
open PEqualNP.Outside.L_meta_4712_aux
open PEqualNP.Outside.L_meta_4712_aux.Partner
open PEqualNP.Outside.L_meta_4712_aux.Transform

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
variable {C : Circuit} {g : ℕ}

lemma dirty_pivot (H : OneDirty G C g) (c : Fin 2) (w : Fin n)
    (single : ∀ y, wireVal n C (opnd C g c) (unitInput y) = true ↔ y = w)
    (x : Fin n → Bool) (hx : gateVal n C g x = true) : x w = true := by
  have h := ((val_and' C H.ao g H.hg H.gand x c).1 hx).1
  rwa [singleton_value H c w single x] at h

lemma active_partner_point (H : OneDirty G C g) (s : Fin n → Bool)
    (bip : ∀ u v, G.Adj u v → s u ≠ s v)
    (c : Fin 2) (w : Fin n)
    (single : ∀ y, wireVal n C (opnd C g c) (unitInput y) = true ↔ y = w)
    (k : ℕ) (hk : k < C.gates.length) (ho : (gateAt C k).op = .and)
    {p q z : Fin n} (hpq : G.Adj p q) (hpz : PZ C g k z)
    (hg : gateVal n C g (pairInput p q) = true)
    (hz : pairInput p q z = true) : s z ≠ s w := by
  have hzw : z ≠ w := by
    intro heq
    subst z
    exact partner_not_singleton H c w single k hk ho hpz
  exact pair_other_color s bip hpq (dirty_pivot H c w single _ hg) hz hzw

lemma same_color_of_opposite (s : Fin n → Bool) {a b w : Fin n}
    (ha : s a ≠ s w) (hb : s b ≠ s w) : s a = s b := by
  cases hsa : s a <;> cases hsb : s b <;> cases hsw : s w <;> simp_all

lemma and_operand_edge_value (H : OneDirty G C g) (s : Fin n → Bool)
    (bip : ∀ u v, G.Adj u v → s u ≠ s v)
    (c : Fin 2) (w : Fin n)
    (single : ∀ y, wireVal n C (opnd C g c) (unitInput y) = true ↔ y = w)
    (noEmpty : ∀ u < n+C.gates.length, Low G C u → u ≠ n+g →
      ∃ y, wireVal n C u (unitInput y) = true)
    (k : ℕ) (hk : k < C.gates.length) (ho : (gateAt C k).op = .and) (hkg : k ≠ g)
    (p q : Fin n) (hpq : G.Adj p q) (hOld : gateVal n C k (pairInput p q) = true)
    (b : Fin 2) :
    (if opnd C k b = n+g then
      if pt C s w (opnd C k (1-b)) then pairInput p q w else false
    else lowVal C s w g (opnd C k b) (pairInput p q)) = true := by
  have hbl := opnd_lt C H.ao k hk b
  have hdl := opnd_lt C H.ao k hk (1-b)
  have hbu : opnd C k b < n+C.gates.length := by omega
  have hdu : opnd C k (1-b) < n+C.gates.length := by omega
  have hlow := low_opnd H k hk b (Or.inr ho)
  have hlow' := low_opnd H k hk (1-b) (Or.inr ho)
  obtain ⟨hLeft, hRight⟩ := (val_and' C H.ao k hk ho _ b).1 hOld
  by_cases hbg : opnd C k b = n+g
  · rw [ite_eq_left hbg]
    have hr : OrReaches n C (opnd C k b) g := by
      rw [hbg]
      exact reach_self C H.ao g H.hg
    have hpure := not_both' H k hk ho b hr
    obtain ⟨z, hz, hzs⟩ := (pure_val H k hk ho (1-b) hpure _).1 hRight
    have hpz : PZ C g k z := (pz_iff C g k z).2 ⟨b, hr, hzs⟩
    have hgp : gateVal n C g (pairInput p q) = true := by
      change wireVal n C (n+g) (pairInput p q) = true
      simpa only [hbg] using hLeft
    have hpoint := active_partner_point H s bip c w single k hk ho hpq hpz hgp hz
    have hpt : pt C s w (opnd C k (1-b)) = true := (pt_iff C s w _).2 ⟨z, hzs, hpoint⟩
    rw [hpt]
    exact dirty_pivot H c w single _ hgp
  · rw [ite_eq_right hbg]
    by_cases hpt : pt C s w (opnd C k b) = true
    · simp only [lowVal, hpt, ite_true]
      apply (pointPart_iff C s w _ _).2
      obtain ⟨a, ha, hap⟩ := (pt_iff C s w _).1 hpt
      rcases (val_low H _ hbu hlow _).1 hLeft with ⟨y, hy, hys⟩ | ⟨hr, hgp⟩
      · refine ⟨y, hy, hys, ?_⟩
        by_cases hdg : opnd C k (1-b) = n+g
        · have hr : OrReaches n C (opnd C k (1-b)) g := by
            rw [hdg]
            exact reach_self C H.ao g H.hg
          have hpz : PZ C g k y := (pz_iff C g k y).2
            ⟨1-b, hr, by simpa only [fin2_inv] using hys⟩
          have hgp : gateVal n C g (pairInput p q) = true := by
            change wireVal n C (n+g) (pairInput p q) = true
            simpa only [hdg] using hRight
          exact active_partner_point H s bip c w single k hk ho hpq hpz hgp hy
        · obtain ⟨z, hzs⟩ := noEmpty _ hdu hlow' hdg
          have hcolor := and_support_homogeneous H s bip k hk ho hkg b hys ha hzs
          exact fun heq => hap (hcolor.symm.trans heq)
      · have hpure := not_both' H k hk ho b hr
        obtain ⟨z, hz, hzs⟩ := (pure_val H k hk ho (1-b) hpure _).1 hRight
        have hpz : PZ C g k z := (pz_iff C g k z).2 ⟨b, hr, hzs⟩
        have hzp := active_partner_point H s bip c w single k hk ho hpq hpz hgp hz
        have hadj := and_pair' H k hk ho hkg b a z ha hzs
        exact False.elim ((bip a z hadj) (same_color_of_opposite s hap hzp))
    · have hptfalse : pt C s w (opnd C k b) = false := Bool.eq_false_iff.mpr hpt
      simp only [lowVal, hptfalse, Bool.false_eq_true, ite_false, Bool.or_eq_true,
        Bool.and_eq_true]
      rcases (val_low H _ hbu hlow _).1 hLeft with hunit | ⟨hr, hgp⟩
      · exact Or.inl ((unitPart_iff C _ _).2 hunit)
      · exact Or.inr ⟨(reaches_iff C g _).2 hr, dirty_pivot H c w single _ hgp⟩

lemma clean_and_edge (H : OneDirty G C g) (s : Fin n → Bool)
    (bip : ∀ u v, G.Adj u v → s u ≠ s v)
    (c : Fin 2) (w : Fin n)
    (single : ∀ y, wireVal n C (opnd C g c) (unitInput y) = true ↔ y = w)
    (noEmpty : ∀ u < n+C.gates.length, Low G C u → u ≠ n+g →
      ∃ y, wireVal n C u (unitInput y) = true)
    (k : ℕ) (hk : k < C.gates.length) (ho : (gateAt C k).op = .and) (hkg : k ≠ g)
    (p q : Fin n) (hpq : G.Adj p q) (hOld : gateVal n C k (pairInput p q) = true) :
    opv (isA (gateAt C k).op)
      (srcAt (pairInput p q) (values G C s w g (pairInput p q)) (route G C s w g k 0))
      (srcAt (pairInput p q) (values G C s w g (pairInput p q)) (route G C s w g k 1)) = true := by
  simp only [ho, isA]
  apply (opv_and _ _).2
  constructor
  · rw [route_and_val H s w k hk ho 0]
    exact and_operand_edge_value H s bip c w single noEmpty k hk ho hkg p q hpq hOld 0
  · rw [route_and_val H s w k hk ho 1]
    exact and_operand_edge_value H s bip c w single noEmpty k hk ho hkg p q hpq hOld 1

end PEqualNP.Outside.L_meta_4712_aux.Transform.Edge

namespace PEqualNP.Outside.L_meta_4712_aux.Transform.Closure

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.MetaComplexity.FoldProg
open PEqualNP.MetaComplexity.LowerPart
open PEqualNP.TopForm PEqualNP.CleanedNonEdge
open PEqualNP.SplitCount (unitInput)
open PEqualNP.EdgeOwnership (gateVal pairInput)
open PEqualNP.Outside.L_meta_4712_aux.Transform

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
variable {C : Circuit} {g : ℕ}

def keepSet (C : Circuit) (g : ℕ) : Finset ℕ := (Finset.range C.gates.length).erase g

lemma route_gate_source (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : Fin n → Bool) (w : Fin n) (g k : ℕ) (b : Fin 2) (j : ℕ)
    (hr : route G C s w g k b = some (Sum.inr j)) :
    srcOf n (opnd C k b) = some (Sum.inr j) := by
  simp only [route] at hr
  split_ifs at hr <;> simp_all

lemma pt_dirty_false (C : Circuit) (s : Fin n → Bool) (w : Fin n) (g : ℕ)
    (hu : ∀ y : Fin n, gateVal n C g (unitInput y) = false) :
    pt C s w (n+g) = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  obtain ⟨y, hy, _⟩ := (pt_iff C s w (n+g)).1 h
  have hf : wireVal n C (n+g) (unitInput y) = false := hu y
  rw [hf] at hy
  cases hy

lemma dirty_reader_or_low (H : OneDirty G C g) (k : ℕ)
    (hk : k < C.gates.length) (ho : (gateAt C k).op = .or)
    (b : Fin 2) (he : opnd C k b = n+g) : lowFlag G C k = true := by
  apply (lowFlag_iff G C k).2
  intro hbelow
  apply H.dirty
  intro x hx
  apply below_or H.ao k hk ho hbelow b x
  rw [he]
  exact hx

lemma route_ne_dirty (H : OneDirty G C g) (s : Fin n → Bool) (w : Fin n)
    (hu : ∀ y : Fin n, gateVal n C g (unitInput y) = false)
    (k : ℕ) (hk : k < C.gates.length) (b : Fin 2) :
    route G C s w g k b ≠ some (Sum.inr g) := by
  by_cases he : opnd C k b = n+g
  · rcases LeafBound.ao_op H.ao hk with ho | ho
    · simp only [route, ho, isA, ite_true, he]
      cases pt C s w (opnd C k (1-b)) <;> simp
    · have hl := dirty_reader_or_low H k hk ho b he
      have hp := pt_dirty_false C s w g hu
      simp only [route, ho, isA, Bool.false_eq_true, ite_false, hl, ite_true, he, hp]
      cases pt C s w (n+k) <;> simp
  · intro hr
    exact he (srcOf_inr _ _ (route_gate_source G C s w g k b g hr))

lemma route_closed (H : OneDirty G C g) (s : Fin n → Bool) (w : Fin n)
    (hu : ∀ y : Fin n, gateVal n C g (unitInput y) = false) :
    ∀ k ∈ keepSet C g, ∀ b : Fin 2, ∀ j : ℕ,
      route G C s w g k b = some (Sum.inr j) → j ∈ keepSet C g ∧ j < k := by
  intro k hk b j hr
  have hkl : k < C.gates.length := Finset.mem_range.mp (Finset.mem_erase.mp hk).2
  have he := srcOf_inr _ _ (route_gate_source G C s w g k b j hr)
  have hback := opnd_lt C H.ao k hkl b
  have hjk : j < k := by omega
  have hjg : j ≠ g := by
    intro h
    subst j
    exact route_ne_dirty H s w hu k hkl b hr
  exact ⟨Finset.mem_erase.mpr ⟨hjg, Finset.mem_range.mpr (by omega)⟩, hjk⟩

lemma output_retained (H : OneDirty G C g) :
    ∀ j, srcOf n C.output = some (Sum.inr j) → j ∈ keepSet C g := by
  intro j hj
  obtain ⟨o, hol, hoo, hob⟩ := out_gate H
  have he := srcOf_inr _ _ hj
  have hjo : j = o := by omega
  subst j
  refine Finset.mem_erase.mpr ⟨?_, Finset.mem_range.mpr hol⟩
  intro h
  subst o
  exact H.dirty hob

lemma output_values (H : OneDirty G C g) (s : Fin n → Bool) (w : Fin n)
    (x : Fin n → Bool) :
    srcAt x (values G C s w g x) (srcOf n C.output) = graphFun G ∅ x := by
  obtain ⟨o, hol, hoo, hob⟩ := out_gate H
  rw [hoo, srcOf_gate]
  change values G C s w g x o = graphFun G ∅ x
  have hl : lowFlag G C o = false := by
    apply Bool.eq_false_iff.mpr
    intro h
    exact ((lowFlag_iff G C o).1 h) hob
  simp only [values, hl, Bool.false_eq_true, ite_false]
  have hc := congrFun H.comp x
  change wireVal n C C.output x = graphFun G ∅ x at hc
  rw [hoo] at hc
  exact hc

lemma graph_has_edge (H : OneDirty G C g) : ∃ u v, G.Adj u v := by
  apply adj_of_AO G C H.ao H.comp
  obtain ⟨o, hol, hoo, _⟩ := out_gate H
  omega

lemma strict_saving (H : OneDirty G C g) (s : Fin n → Bool) (w : Fin n) :
    ∃ k < C.gates.length, k ∉ keepSet C g ∨ ∃ b, route G C s w g k b = none := by
  exact ⟨g, H.hg, Or.inl (by simp [keepSet])⟩

end PEqualNP.Outside.L_meta_4712_aux.Transform.Closure

namespace PEqualNP.Outside.L_meta_4712_aux.Transform.Finish

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.MetaComplexity.FoldProg
open PEqualNP.MetaComplexity.LowerPart
open PEqualNP.TopForm PEqualNP.CleanedNonEdge
open PEqualNP.SplitCount (unitInput)
open PEqualNP.EdgeOwnership (gateVal pairInput)

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
variable {C : Circuit} {g : ℕ}

theorem added_partner_adj (H : OneDirty G C g) (s : Fin n → Bool)
    (bip : ∀ u v, G.Adj u v → s u ≠ s v)
    (d : Fin 2) (w : Fin n)
    (single : ∀ y, wireVal n C (opnd C g d) (unitInput y) = true ↔ y = w)
    (opposite : ∀ y, wireVal n C (opnd C g (1-d)) (unitInput y) = true → s y ≠ s w)
    (nonempty : ∀ u < n+C.gates.length, Low G C u → u ≠ n+g →
      ∃ y, wireVal n C u (unitInput y) = true)
    (k : ℕ) (hk : k < C.gates.length) (hand : (gateAt C k).op = .and)
    (hkg : k ≠ g) (b : Fin 2) (hne : opnd C k b ≠ n+g)
    (hp : pt C s w (opnd C k b) = false)
    (hr : OrReaches n C (opnd C k b) g) (z : Fin n)
    (hz : wireVal n C (opnd C k (1-b)) (unitInput z) = true) : G.Adj w z := by
  have hb := opnd_lt C H.ao k hk b
  obtain ⟨a, ha⟩ := nonempty (opnd C k b) (by omega)
    (low_opnd H k hk b (Or.inr hand)) hne
  have hac := color_of_not_pt C s w (opnd C k b) hp a ha
  have haz := and_pair' H k hk hand hkg b a z ha hz
  have hzc : s z ≠ s w := by
    intro e
    exact bip a z haz (hac.trans e.symm)
  exact partner_opposite_adj H s bip d w single opposite k hk hand z
    ((pz_iff C g k z).2 ⟨b, hr, hz⟩) hzc

theorem and_expr_safe (H : OneDirty G C g) (s : Fin n → Bool)
    (bip : ∀ u v, G.Adj u v → s u ≠ s v)
    (d : Fin 2) (w : Fin n)
    (single : ∀ y, wireVal n C (opnd C g d) (unitInput y) = true ↔ y = w)
    (opposite : ∀ y, wireVal n C (opnd C g (1-d)) (unitInput y) = true → s y ≠ s w)
    (nonempty : ∀ u < n+C.gates.length, Low G C u → u ≠ n+g →
      ∃ y, wireVal n C u (unitInput y) = true)
    (k : ℕ) (hk : k < C.gates.length) (hand : (gateAt C k).op = .and)
    (hkg : k ≠ g) (x : Fin n → Bool)
    (on : ∀ b : Fin 2,
      (if opnd C k b = n+g then
        (if pt C s w (opnd C k (1-b)) then x w else false)
       else lowVal C s w g (opnd C k b) x) = true) : graphFun G ∅ x = true := by
  have direct (b : Fin 2) (he : opnd C k b = n+g) : graphFun G ∅ x = true := by
    have hr : OrReaches n C (opnd C k b) g := by
      rw [he]
      exact reach_self C H.ao g H.hg
    have hother : opnd C k (1-b) ≠ n+g := by
      intro e
      apply not_both' H k hk hand b hr
      rw [e]
      exact reach_self C H.ao g H.hg
    have hb := on b
    rw [if_pos he] at hb
    have hp : pt C s w (opnd C k (1-b)) = true := by
      by_contra hp
      have hpf : pt C s w (opnd C k (1-b)) = false := Bool.eq_false_iff.mpr hp
      rw [hpf] at hb
      cases hb
    have hw : x w = true := by simpa [hp] using hb
    have ho : lowVal C s w g (opnd C k (1-b)) x = true := by
      simpa [hother] using on (1-b)
    obtain ⟨z, hzx, hz, hzc⟩ := lowVal_point C s w g _ x hp ho
    have adj := partner_opposite_adj H s bip d w single opposite k hk hand z
      ((pz_iff C g k z).2 ⟨b, hr, hz⟩) hzc
    exact (graphFun_empty G x).2 ⟨w, z, adj, hw, hzx⟩
  by_cases h0 : opnd C k 0 = n+g
  · exact direct 0 h0
  by_cases h1 : opnd C k 1 = n+g
  · exact direct 1 h1
  have v0 : lowVal C s w g (opnd C k 0) x = true := by simpa [h0] using on 0
  have v1 : lowVal C s w g (opnd C k 1) x = true := by simpa [h1] using on 1
  rcases lowVal_cases C s w g _ x v0 with ⟨y, hyx, hy⟩ | ⟨hp0, hr0, hw0⟩
  · rcases lowVal_cases C s w g _ x v1 with ⟨z, hzx, hz⟩ | ⟨hp1, hr1, hw1⟩
    · exact (graphFun_empty G x).2 ⟨y, z, and_pair H k hk hand hkg y z hy hz, hyx, hzx⟩
    · have adj := added_partner_adj H s bip d w single opposite nonempty k hk hand hkg
        1 h1 hp1 hr1 y hy
      exact (graphFun_empty G x).2 ⟨w, y, adj, hw1, hyx⟩
  · rcases lowVal_cases C s w g _ x v1 with ⟨z, hzx, hz⟩ | ⟨hp1, hr1, hw1⟩
    · have adj := added_partner_adj H s bip d w single opposite nonempty k hk hand hkg
        0 h0 hp0 hr0 z hz
      exact (graphFun_empty G x).2 ⟨w, z, adj, hw0, hzx⟩
    · exact False.elim (not_both H k hk hand ⟨hr0, hr1⟩)

theorem clean_and_safe (H : OneDirty G C g) (s : Fin n → Bool)
    (bip : ∀ u v, G.Adj u v → s u ≠ s v)
    (d : Fin 2) (w : Fin n)
    (single : ∀ y, wireVal n C (opnd C g d) (unitInput y) = true ↔ y = w)
    (opposite : ∀ y, wireVal n C (opnd C g (1-d)) (unitInput y) = true → s y ≠ s w)
    (nonempty : ∀ u < n+C.gates.length, Low G C u → u ≠ n+g →
      ∃ y, wireVal n C u (unitInput y) = true)
    (k : ℕ) (hk : k < C.gates.length) (hand : (gateAt C k).op = .and)
    (hkg : k ≠ g) (x : Fin n → Bool)
    (hval : opv (isA (gateAt C k).op)
      (srcAt x (values G C s w g x) (route G C s w g k 0))
      (srcAt x (values G C s w g x) (route G C s w g k 1)) = true) :
    graphFun G ∅ x = true := by
  have hh : srcAt x (values G C s w g x) (route G C s w g k 0) = true ∧
      srcAt x (values G C s w g x) (route G C s w g k 1) = true := by
    simpa [hand, isA, opv] using hval
  apply and_expr_safe H s bip d w single opposite nonempty k hk hand hkg x
  intro b
  rw [← route_and_val H s w k hk hand b x]
  fin_cases b
  · exact hh.1
  · exact hh.2

theorem flag_false_of_below (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (k : ℕ) (hb : BelowF G C k) : lowFlag G C k = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  exact ((lowFlag_iff G C k).1 h) hb

theorem shorten (H : OneDirty G C g) (s : Fin n → Bool)
    (bip : ∀ u v, G.Adj u v → s u ≠ s v)
    (d : Fin 2) (w : Fin n)
    (single : ∀ y, wireVal n C (opnd C g d) (unitInput y) = true ↔ y = w)
    (opposite : ∀ y, wireVal n C (opnd C g (1-d)) (unitInput y) = true → s y ≠ s w)
    (hu : ∀ y : Fin n, gateVal n C g (unitInput y) = false) : Smaller G C := by
  classical
  by_contra hmin
  have noEmpty : ∀ u < n+C.gates.length, Low G C u → u ≠ n+g →
      ∃ y, wireVal n C u (unitInput y) = true :=
    Partner.low_support_nonempty_of_not_smaller H hmin
  have hK : ∀ k ∈ Closure.keepSet C g, k < C.gates.length := by
    intro k hk
    exact Finset.mem_range.mp (Finset.mem_erase.mp hk).2
  have neK : ∀ k ∈ Closure.keepSet C g, k ≠ g := by
    intro k hk
    exact (Finset.mem_erase.mp hk).1
  apply hmin
  refine redirect_lt G C (Closure.keepSet C g) hK (route G C s w g)
    (Closure.route_closed H s w hu) (srcOf n C.output) (Closure.output_retained H)
    (Closure.graph_has_edge H) ?_ ?_ (Closure.strict_saving H s w)
  · intro x hfalse
    refine ⟨values G C s w g x, ?_, ?_⟩
    · intro k hk hv
      change opv (isA (gateAt C k).op)
        (srcAt x (values G C s w g x) (route G C s w g k 0))
        (srcAt x (values G C s w g x) (route G C s w g k 1)) = true at hv
      rcases LeafBound.ao_op H.ao (hK k hk) with hand | hor
      · have hf := clean_and_safe H s bip d w single opposite noEmpty k (hK k hk)
          hand (neK k hk) x hv
        rw [hfalse] at hf
        contradiction
      · by_cases hl : Low G C (n+k)
        · rw [low_or_equation H s w hu k (hK k hk) hor hl x] at hv
          simpa only [values, (lowFlag_iff G C k).2 hl, ite_true] using hv
        · have hb : BelowF G C k := by
            by_contra h
            exact hl h
          rw [high_or_equation H s w k (hK k hk) hor hb x] at hv
          simpa only [values, flag_false_of_below G C k hb, Bool.false_eq_true, ite_false] using hv
    · rw [Closure.output_values H s w x]
      exact hfalse
  · intro p q hpq
    refine ⟨values G C s w g (pairInput p q), ?_, ?_⟩
    · intro k hk hv
      change opv (isA (gateAt C k).op)
        (srcAt (pairInput p q) (values G C s w g (pairInput p q)) (route G C s w g k 0))
        (srcAt (pairInput p q) (values G C s w g (pairInput p q)) (route G C s w g k 1)) = true
      rcases LeafBound.ao_op H.ao (hK k hk) with hand | hor
      · have hb := H.others k (hK k hk) hand (neK k hk)
        have hold : gateVal n C k (pairInput p q) = true := by
          simpa only [values, flag_false_of_below G C k hb, Bool.false_eq_true, ite_false] using hv
        exact Edge.clean_and_edge H s bip d w single noEmpty k (hK k hk) hand (neK k hk) p q hpq hold
      · by_cases hl : Low G C (n+k)
        · rw [low_or_equation H s w hu k (hK k hk) hor hl (pairInput p q)]
          simpa only [values, (lowFlag_iff G C k).2 hl, ite_true] using hv
        · have hb : BelowF G C k := by
            by_contra h
            exact hl h
          rw [high_or_equation H s w k (hK k hk) hor hb (pairInput p q)]
          simpa only [values, flag_false_of_below G C k hb, Bool.false_eq_true, ite_false] using hv
    · rw [Closure.output_values H s w (pairInput p q)]
      exact (graphFun_empty G _).2 ⟨p, q, hpq, by simp [pairInput], by simp [pairInput]⟩

end PEqualNP.Outside.L_meta_4712_aux.Transform.Finish

theorem PEqualNP.Outside.L_meta_4712 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit) (s : Fin n → Bool) (g : ℕ), (∀ u v : Fin n, G.Adj u v → s u ≠ s v) → PEqualNP.TopForm.NoFourCycle G → PEqualNP.TopForm.IsAO2 n C → PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ → PEqualNP.Core.IsLiftFixedPoint G C → (∀ k < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ t ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs, ¬ (∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨C.gates, t⟩ (List.ofFn x) = true → PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x = true)) → (∀ k < C.gates.length, PEqualNP.Core.InOutputCone n C k) → g < C.gates.length → (PEqualNP.MetaComplexity.NestedCover.gateAt C g).op = PEqualNP.CircuitLowerBounds.GateOp.and → ¬ PEqualNP.TopForm.BelowF G C g → (∀ k < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.and → k ≠ g → PEqualNP.TopForm.BelowF G C k) → (∀ w : Fin n, PEqualNP.EdgeOwnership.gateVal n C g (PEqualNP.SplitCount.unitInput w) = false) → ((∃ w : Fin n, (∀ y : Fin n, PEqualNP.CleanedNonEdge.wireVal n C (PEqualNP.TopForm.opnd C g 1) (PEqualNP.SplitCount.unitInput y) = true ↔ y = w) ∧ ∀ y : Fin n, PEqualNP.CleanedNonEdge.wireVal n C (PEqualNP.TopForm.opnd C g 0) (PEqualNP.SplitCount.unitInput y) = true → s y ≠ s w) ∨ (∃ w : Fin n, (∀ y : Fin n, PEqualNP.CleanedNonEdge.wireVal n C (PEqualNP.TopForm.opnd C g 0) (PEqualNP.SplitCount.unitInput y) = true ↔ y = w) ∧ ∀ y : Fin n, PEqualNP.CleanedNonEdge.wireVal n C (PEqualNP.TopForm.opnd C g 1) (PEqualNP.SplitCount.unitInput y) = true → s y ≠ s w)) → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 n D ∧ D.size < C.size ∧ PEqualNP.MetaComplexity.circuitFun n D = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ := by
  intro n G inst C s g bip _noFour ao comp lift andLow cone hg gand dirty others hu orient
  let H : PEqualNP.MetaComplexity.LowerPart.OneDirty G C g :=
    ⟨ao, comp, lift, andLow, cone, hg, gand, dirty, others⟩
  rcases orient with ⟨w, single, opposite⟩ | ⟨w, single, opposite⟩
  · exact PEqualNP.Outside.L_meta_4712_aux.Transform.Finish.shorten H s bip 1 w single opposite hu
  · exact PEqualNP.Outside.L_meta_4712_aux.Transform.Finish.shorten H s bip 0 w single opposite hu
