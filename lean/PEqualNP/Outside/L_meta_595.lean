import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_595

open PEqualNP.CircuitLowerBounds

/-- truth table of g restricted to the point list ps; bit k = g (ps[k]) -/
def encL (g : (Fin 7 → Bool) → Bool) : List (Fin 7 → Bool) → ℕ
  | [] => 0
  | p :: ps => Nat.bit (g p) (encL g ps)

/-- gate value on encoded tables; A = encL (fun _ => true) ps is the all-ones table.
  o = 0: AND, 1: OR, 2: NOT of the first, 3: NOT of the second -/
def opv (A : ℕ) (o : Fin 4) (a b : ℕ) : ℕ :=
  match o with
  | 0 => a &&& b
  | 1 => a ||| b
  | 2 => A ^^^ a
  | 3 => A ^^^ b

def kept (k : Bool) (x : ℕ) (xs : List ℕ) : List ℕ := if k then x :: xs else xs

/-- Run T A s L: from the live multiset L, s more gates suffice to reach [T] (forward direction). -/
inductive Run (T A : ℕ) : ℕ → List ℕ → Prop
  | done (s : ℕ) : Run T A s [T]
  | perm {s : ℕ} {L₁ L₂ : List ℕ} : L₁.Perm L₂ → Run T A s L₁ → Run T A s L₂
  | mono {s : ℕ} {L : List ℕ} : Run T A s L → Run T A (s + 1) L
  | two {s a b : ℕ} {r : List ℕ} (o : Fin 4) (ka kb : Bool) :
      Run T A s (opv A o a b :: kept ka a (kept kb b r)) → Run T A (s + 1) (a :: b :: r)
  | one {s a w : ℕ} {r : List ℕ} (ka : Bool) : (w = a ∨ w = A ^^^ a ∨ w = 0 ∨ w = A) →
      Run T A s (w :: kept ka a r) → Run T A (s + 1) (a :: r)
  | const {s w : ℕ} {r : List ℕ} : (w = 0 ∨ w = A) → Run T A s (w :: r) → Run T A (s + 1) r

/-- encoded input variable i -/
def Xv (ps : List (Fin 7 → Bool)) (i : ℕ) : ℕ :=
  encL (fun x => if h : i < 7 then x ⟨i, h⟩ else false) ps


theorem encL_and (g h : (Fin 7 → Bool) → Bool) : ∀ l : List (Fin 7 → Bool),
    encL (fun x => g x && h x) l = encL g l &&& encL h l
  | [] => by simp [encL]
  | p :: ps => by simp only [encL, Nat.land_bit, encL_and g h ps]

theorem encL_or (g h : (Fin 7 → Bool) → Bool) : ∀ l : List (Fin 7 → Bool),
    encL (fun x => g x || h x) l = encL g l ||| encL h l
  | [] => by simp [encL]
  | p :: ps => by simp only [encL, Nat.lor_bit, encL_or g h ps]

theorem encL_false : ∀ l : List (Fin 7 → Bool), encL (fun _ => false) l = 0
  | [] => rfl
  | p :: ps => by simp only [encL, encL_false ps]; rfl

theorem encL_not (g : (Fin 7 → Bool) → Bool) : ∀ l : List (Fin 7 → Bool),
    encL (fun x => !g x) l = encL (fun _ => true) l ^^^ encL g l
  | [] => by simp [encL]
  | p :: ps => by
    simp only [encL, Nat.xor_bit, encL_not g ps]
    congr 1
    cases g p <;> rfl

def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl stp x := rfl

theorem foldl_pre : ∀ (gs : List Gate) (x : List Bool), ∃ ys,
    gs.foldl stp x = x ++ ys ∧ ys.length = gs.length
  | [], x => ⟨[], by simp⟩
  | g :: gs, x => by
    obtain ⟨ys, h1, h2⟩ := foldl_pre gs (stp x g)
    refine ⟨g.op.eval (g.inputs.map fun i => x.getD i false) :: ys, ?_, by simp [h2]⟩
    rw [List.foldl_cons, h1]
    simp [stp]

theorem foldl_gate (gs : List Gate) (x : List Bool) (j : ℕ) (g : Gate) (hg : gs[j]? = some g) :
    (gs.foldl stp x).getD (x.length + j) false =
      g.op.eval (g.inputs.map fun i => if i < x.length + j then (gs.foldl stp x).getD i false
        else false) := by
  have hj : j < gs.length := by
    by_contra h
    rw [List.getElem?_eq_none (by omega)] at hg
    cases hg
  have hsplit : gs = gs.take j ++ g :: gs.drop (j + 1) := by
    conv_lhs => rw [← List.take_append_drop j gs]
    rw [List.drop_eq_getElem_cons hj]
    rw [List.getElem?_eq_getElem hj] at hg
    cases hg
    rfl
  obtain ⟨ys, h1, h2⟩ := foldl_pre (gs.take j) x
  have hlen : (x ++ ys).length = x.length + j := by
    simp [h2, List.length_take]
    omega
  generalize hw : x ++ ys = w at h1 hlen
  obtain ⟨zs, h3, _⟩ := foldl_pre (gs.drop (j + 1)) (stp w g)
  generalize hv : g.op.eval (g.inputs.map fun i => w.getD i false) = v
  have hfin : gs.foldl stp x = w ++ ([v] ++ zs) := by
    rw [hsplit, List.foldl_append, h1, List.foldl_cons, h3, ← hv]
    simp [stp]
  rw [hfin, ← hlen, List.getD_append_right _ _ _ _ (le_refl _), Nat.sub_self]
  show v = _
  rw [← hv]
  congr 1
  apply List.map_congr_left
  intro i _
  by_cases hi : i < w.length
  · rw [if_pos hi, List.getD_append _ _ _ _ hi]
  · rw [if_neg hi]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_none (by omega)]
    rfl

theorem wires_len (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.gates.length := by
  obtain ⟨ys, h1, h2⟩ := foldl_pre C.gates x
  rw [wires_eq, h1]
  simp [h2]

def W (C : Circuit) (i : ℕ) (x : Fin 7 → Bool) : Bool := (C.wires (List.ofFn x)).getD i false

theorem W_input (C : Circuit) (i : ℕ) (hi : i < 7) (x : Fin 7 → Bool) : W C i x = x ⟨i, hi⟩ := by
  obtain ⟨ys, h1, _⟩ := foldl_pre C.gates (List.ofFn x)
  rw [W, wires_eq, h1, List.getD_append _ _ _ _ (by simp [hi])]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp [hi]

theorem W_gate (C : Circuit) (j : ℕ) (g : Gate) (hg : C.gates[j]? = some g) (x : Fin 7 → Bool) :
    W C (7 + j) x = g.op.eval (g.inputs.map fun i => if i < 7 + j then W C i x else false) := by
  have := foldl_gate C.gates (List.ofFn x) j g hg
  simp only [List.length_ofFn] at this
  simp only [W, wires_eq]
  exact this

def val (ps : List (Fin 7 → Bool)) (C : Circuit) (i : ℕ) : ℕ := encL (W C i) ps

theorem val_input (ps : List (Fin 7 → Bool)) (C : Circuit) (i : ℕ) (hi : i < 7) :
    val ps C i = Xv ps i := by
  unfold val Xv
  congr 1
  funext x
  rw [W_input C i hi, dif_pos hi]

theorem enc_rd (ps : List (Fin 7 → Bool)) (C : Circuit) (t i : ℕ) :
    encL (fun x => if i < 7 + t then W C i x else false) ps = if i < 7 + t then val ps C i else 0 := by
  by_cases h : i < 7 + t
  · simp only [h, if_true]; rfl
  · simp only [h, if_false]; exact encL_false _

theorem val_gate (ps : List (Fin 7 → Bool)) (C : Circuit) (t : ℕ) (g : Gate)
    (hg : C.gates[t]? = some g) :
    val ps C (7 + t) = encL (fun x => g.op.eval
      (g.inputs.map fun i => if i < 7 + t then W C i x else false)) ps := by
  unfold val
  congr 1
  funext x
  exact W_gate C t g hg x

def gIn (C : Circuit) (t : ℕ) : Finset ℕ :=
  match C.gates[t]? with
  | some g => (g.inputs.filter (fun i => decide (i < 7 + t))).toFinset
  | none => ∅

theorem mem_gIn {C : Circuit} {t : ℕ} {g : Gate} (hg : C.gates[t]? = some g) (w : ℕ) :
    w ∈ gIn C t ↔ w ∈ g.inputs ∧ w < 7 + t := by
  unfold gIn
  rw [hg]
  simp

def need (C : Circuit) : ℕ → Finset ℕ
  | 0 => {C.output}
  | d + 1 =>
    if 7 + (C.gates.length - (d + 1)) ∈ need C d then
      (need C d).erase (7 + (C.gates.length - (d + 1))) ∪ gIn C (C.gates.length - (d + 1))
    else need C d

noncomputable def St (ps : List (Fin 7 → Bool)) (C : Circuit) (d : ℕ) : List ℕ :=
  (need C d).toList.map (val ps C)

theorem need_bound (C : Circuit) (ho : C.output < 7 + C.gates.length) :
    ∀ d, d ≤ C.gates.length → ∀ w ∈ need C d, w < 7 + (C.gates.length - d)
  | 0, _, w, hw => by
    simp only [need, Finset.mem_singleton] at hw
    omega
  | d + 1, hd, w, hw => by
    have ih := need_bound C ho d (by omega)
    unfold need at hw
    split at hw
    · rw [Finset.mem_union, Finset.mem_erase] at hw
      rcases hw with ⟨h1, h2⟩ | h
      · have := ih w h2
        omega
      · unfold gIn at h
        split at h
        · simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq] at h
          omega
        · simp at h
    · rename_i hn
      have := ih w hw
      have : w ≠ 7 + (C.gates.length - (d + 1)) := fun e => hn (e ▸ hw)
      omega

theorem mem_kept {k : Bool} {x v : ℕ} {xs : List ℕ} (h : v ∈ kept k x xs) : v = x ∨ v ∈ xs := by
  cases k
  · exact Or.inr h
  · simpa [kept] using h

theorem mem_kept_iff {k : Bool} {x v : ℕ} {xs : List ℕ} :
    v ∈ kept k x xs ↔ (k = true ∧ v = x) ∨ v ∈ xs := by
  cases k <;> simp [kept]

theorem map_kept (f : ℕ → ℕ) (k : Bool) (x : ℕ) (xs : List ℕ) :
    (kept k x xs).map f = kept k (f x) (xs.map f) := by
  cases k <;> rfl

theorem toL_perm {A : Finset ℕ} {L : List ℕ} (hL : L.Nodup) (h : ∀ w, w ∈ A ↔ w ∈ L) :
    A.toList.Perm L :=
  (List.perm_ext_iff_of_nodup (Finset.nodup_toList A) hL).2
    (fun w => by rw [Finset.mem_toList]; exact h w)

theorem H0 {T AA d : ℕ} {A I : Finset ℕ} {f : ℕ → ℕ} {w : ℕ} (hI : ∀ x, x ∉ I)
    (hw : w = 0 ∨ w = AA) (h : Run T AA d (w :: A.toList.map f)) :
    Run T AA (d + 1) ((A ∪ I).toList.map f) := by
  have e : A ∪ I = A := by
    ext x
    simp [hI x]
  rw [e]
  exact Run.const hw h

theorem H1 {T AA d : ℕ} {A I : Finset ℕ} {f : ℕ → ℕ} {a w : ℕ} (hI : ∀ x, x ∈ I ↔ x = a)
    (hw : w = f a ∨ w = AA ^^^ f a ∨ w = 0 ∨ w = AA) (h : Run T AA d (w :: A.toList.map f)) :
    Run T AA (d + 1) ((A ∪ I).toList.map f) := by
  by_cases ha : a ∈ A
  · have p1 : A.toList.Perm (a :: (A.erase a).toList) := by
      apply toL_perm (List.nodup_cons.2 ⟨by simp, Finset.nodup_toList _⟩)
      intro x
      simp only [List.mem_cons, Finset.mem_toList, Finset.mem_erase]
      constructor
      · intro hx
        by_cases e : x = a
        · exact Or.inl e
        · exact Or.inr ⟨e, hx⟩
      · rintro (rfl | ⟨_, hx⟩)
        · exact ha
        · exact hx
    have p2 : (A ∪ I).toList.Perm (a :: (A.erase a).toList) := by
      refine List.Perm.trans ?_ p1
      have e : A ∪ I = A := by
        ext x
        rw [Finset.mem_union, hI]
        constructor
        · rintro (h | rfl)
          · exact h
          · exact ha
        · exact Or.inl
      rw [e]
    have q : Run T AA d (w :: kept true (f a) ((A.erase a).toList.map f)) := by
      refine Run.perm ?_ h
      have := (p1.map f).cons w
      simpa [kept] using this
    have r := Run.one (r := (A.erase a).toList.map f) true hw q
    exact Run.perm ((p2.map f).symm) (by simpa using r)
  · have p2 : (A ∪ I).toList.Perm (a :: A.toList) := by
      apply toL_perm (List.nodup_cons.2 ⟨by simp [ha], Finset.nodup_toList _⟩)
      intro x
      rw [Finset.mem_union, hI, List.mem_cons, Finset.mem_toList]
      tauto
    have r := Run.one (r := A.toList.map f) false hw (by simpa [kept] using h)
    exact Run.perm ((p2.map f).symm) (by simpa using r)

theorem H2 {T AA d : ℕ} {A I : Finset ℕ} {f : ℕ → ℕ} {a b : ℕ} (o : Fin 4) (hab : a ≠ b)
    (hI : ∀ x, x ∈ I ↔ x = a ∨ x = b)
    (h : Run T AA d (opv AA o (f a) (f b) :: A.toList.map f)) :
    Run T AA (d + 1) ((A ∪ I).toList.map f) := by
  let Rs := (A.erase a).erase b
  have hR : ∀ x, x ∈ Rs ↔ x ∈ A ∧ x ≠ a ∧ x ≠ b := by
    intro x
    simp only [Rs, Finset.mem_erase]
    tauto
  have nR : Rs.toList.Nodup := Finset.nodup_toList _
  have p1 : A.toList.Perm (kept (decide (a ∈ A)) a (kept (decide (b ∈ A)) b Rs.toList)) := by
    have n1 : (kept (decide (b ∈ A)) b Rs.toList).Nodup := by
      cases hb : decide (b ∈ A)
      · exact nR
      · exact List.nodup_cons.2 ⟨by rw [Finset.mem_toList, hR]; tauto, nR⟩
    have n2 : (kept (decide (a ∈ A)) a (kept (decide (b ∈ A)) b Rs.toList)).Nodup := by
      cases ha : decide (a ∈ A)
      · exact n1
      · refine List.nodup_cons.2 ⟨?_, n1⟩
        intro hm
        rcases mem_kept hm with e | hm
        · exact hab e
        · rw [Finset.mem_toList, hR] at hm
          exact hm.2.1 rfl
    apply toL_perm n2
    intro x
    simp only [mem_kept_iff, decide_eq_true_eq, Finset.mem_toList, hR]
    constructor
    · intro hx
      by_cases e1 : x = a
      · exact Or.inl ⟨e1 ▸ hx, e1⟩
      by_cases e2 : x = b
      · exact Or.inr (Or.inl ⟨e2 ▸ hx, e2⟩)
      exact Or.inr (Or.inr ⟨hx, e1, e2⟩)
    · rintro (⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨h1, _⟩) <;> exact h1
  have p2 : (A ∪ I).toList.Perm (a :: b :: Rs.toList) := by
    have hn : (a :: b :: Rs.toList).Nodup := by
      refine List.nodup_cons.2 ⟨?_, List.nodup_cons.2 ⟨?_, nR⟩⟩
      · simp only [List.mem_cons, Finset.mem_toList, hR]
        tauto
      · simp only [Finset.mem_toList, hR]
        tauto
    apply toL_perm hn
    intro x
    simp only [Finset.mem_union, hI, List.mem_cons, Finset.mem_toList, hR]
    tauto
  have q : Run T AA d (opv AA o (f a) (f b) :: kept (decide (a ∈ A)) (f a)
      (kept (decide (b ∈ A)) (f b) (Rs.toList.map f))) := by
    refine Run.perm ?_ h
    have := (p1.map f).cons (opv AA o (f a) (f b))
    simpa [map_kept] using this
  have r := Run.two o _ _ q
  exact Run.perm ((p2.map f).symm) (by simpa using r)

theorem eval_and2 (b1 b2 : Bool) : GateOp.eval GateOp.and [b1, b2] = (b1 && b2) := by
  cases b1 <;> cases b2 <;> rfl
theorem eval_or2 (b1 b2 : Bool) : GateOp.eval GateOp.or [b1, b2] = (b1 || b2) := by
  cases b1 <;> cases b2 <;> rfl
theorem eval_and1 (b : Bool) : GateOp.eval GateOp.and [b] = b := by cases b <;> rfl
theorem eval_or1 (b : Bool) : GateOp.eval GateOp.or [b] = b := by cases b <;> rfl
theorem eval_not_cons (b : Bool) (l : List Bool) : GateOp.eval GateOp.not (b :: l) = !b := rfl

theorem rd_enc (ps : List (Fin 7 → Bool)) (C : Circuit) (t i : ℕ) (hi : i < 7 + t) :
    encL (fun x => if i < 7 + t then W C i x else false) ps = val ps C i := by
  rw [enc_rd, if_pos hi]

theorem rd_enc0 (ps : List (Fin 7 → Bool)) (C : Circuit) (t i : ℕ) (hi : ¬ i < 7 + t) :
    encL (fun x => if i < 7 + t then W C i x else false) ps = 0 := by
  rw [enc_rd, if_neg hi]

theorem opv_aa (AA a : ℕ) (o : Fin 4) :
    opv AA o a a = a ∨ opv AA o a a = AA ^^^ a ∨ opv AA o a a = 0 ∨ opv AA o a a = AA := by
  fin_cases o <;> simp [opv]

theorem opv_a0 (AA a : ℕ) (o : Fin 4) :
    opv AA o a 0 = a ∨ opv AA o a 0 = AA ^^^ a ∨ opv AA o a 0 = 0 ∨ opv AA o a 0 = AA := by
  fin_cases o <;> simp [opv]

theorem opv_0b (AA b : ℕ) (o : Fin 4) :
    opv AA o 0 b = b ∨ opv AA o 0 b = AA ^^^ b ∨ opv AA o 0 b = 0 ∨ opv AA o 0 b = AA := by
  fin_cases o <;> simp [opv]

theorem opv_00 (AA : ℕ) (o : Fin 4) : opv AA o 0 0 = 0 ∨ opv AA o 0 0 = AA := by
  fin_cases o <;> simp [opv]

theorem fin2 (ps : List (Fin 7 → Bool)) (T : ℕ) (C : Circuit) {t d : ℕ} {A : Finset ℕ}
    {i i2 : ℕ} (o : Fin 4)
    (hI : ∀ x, x ∈ gIn C t ↔ (x = i ∨ x = i2) ∧ x < 7 + t)
    (ho : val ps C (7 + t) = opv (encL (fun _ => true) ps) o
      (encL (fun x => if i < 7 + t then W C i x else false) ps)
      (encL (fun x => if i2 < 7 + t then W C i2 x else false) ps))
    (h : Run T (encL (fun _ => true) ps) d (val ps C (7 + t) :: A.toList.map (val ps C))) :
    Run T (encL (fun _ => true) ps) (d + 1) ((A ∪ gIn C t).toList.map (val ps C)) := by
  by_cases h1 : i < 7 + t <;> by_cases h2 : i2 < 7 + t
  · rw [rd_enc ps C t i h1, rd_enc ps C t i2 h2] at ho
    by_cases h12 : i = i2
    · subst h12
      refine H1 (a := i) (fun x => ?_) ?_ h
      · rw [hI]
        constructor
        · rintro ⟨rfl | rfl, _⟩ <;> rfl
        · rintro rfl
          exact ⟨Or.inl rfl, h1⟩
      · rw [ho]
        exact opv_aa _ _ o
    · refine H2 o h12 (fun x => ?_) (by rw [← ho]; exact h)
      rw [hI]
      constructor
      · exact fun h' => h'.1
      · rintro (rfl | rfl)
        · exact ⟨Or.inl rfl, h1⟩
        · exact ⟨Or.inr rfl, h2⟩
  · rw [rd_enc ps C t i h1, rd_enc0 ps C t i2 h2] at ho
    refine H1 (a := i) (fun x => ?_) ?_ h
    · rw [hI]
      constructor
      · rintro ⟨rfl | rfl, hx⟩
        · rfl
        · exact absurd hx h2
      · rintro rfl
        exact ⟨Or.inl rfl, h1⟩
    · rw [ho]
      exact opv_a0 _ _ o
  · rw [rd_enc0 ps C t i h1, rd_enc ps C t i2 h2] at ho
    refine H1 (a := i2) (fun x => ?_) ?_ h
    · rw [hI]
      constructor
      · rintro ⟨rfl | rfl, hx⟩
        · exact absurd hx h1
        · rfl
      · rintro rfl
        exact ⟨Or.inr rfl, h2⟩
    · rw [ho]
      exact opv_0b _ _ o
  · rw [rd_enc0 ps C t i h1, rd_enc0 ps C t i2 h2] at ho
    refine H0 (fun x hx => ?_) ?_ h
    · rw [hI] at hx
      rcases hx with ⟨rfl | rfl, hx⟩
      · exact h1 hx
      · exact h2 hx
    · rw [ho]
      exact opv_00 _ o

theorem gate_step (ps : List (Fin 7 → Bool)) (T : ℕ) (C : Circuit)
    (hF : PEqualNP.MetaComplexity.FanInTwo C) {t d : ℕ} {g : Gate}
    (hg : C.gates[t]? = some g) {A : Finset ℕ}
    (h : Run T (encL (fun _ => true) ps) d (val ps C (7 + t) :: A.toList.map (val ps C))) :
    Run T (encL (fun _ => true) ps) (d + 1) ((A ∪ gIn C t).toList.map (val ps C)) := by
  have hmem : g ∈ C.gates := List.mem_of_getElem? hg
  obtain ⟨hop, hlen⟩ := hF g hmem
  have hop3 : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not := by simpa using hop
  have hv := val_gate ps C t g hg
  have hI := mem_gIn hg
  rcases hin : g.inputs with _ | ⟨i, _ | ⟨i2, _ | ⟨i3, rest⟩⟩⟩
  · rw [hin] at hv hI
    refine H0 (fun x hx => by simp [hI] at hx) ?_ h
    rw [hv]
    rcases hop3 with e | e | e <;> rw [e]
    · right; rfl
    · left; exact encL_false ps
    · right; rfl
  · rw [hin] at hv hI
    simp only [List.map_cons, List.map_nil] at hv
    have hI2 : ∀ x, x ∈ gIn C t ↔ (x = i ∨ x = i) ∧ x < 7 + t := by
      intro x
      rw [hI]
      simp
    rcases hop3 with e | e | e
    · refine fin2 ps T C (i := i) (i2 := i) 0 hI2 ?_ h
      rw [hv, e]
      simp only [eval_and1]
      simp [opv]
    · refine fin2 ps T C (i := i) (i2 := i) 1 hI2 ?_ h
      rw [hv, e]
      simp only [eval_or1]
      simp [opv]
    · refine fin2 ps T C (i := i) (i2 := i) 2 hI2 ?_ h
      rw [hv, e]
      simp only [eval_not_cons]
      exact encL_not _ ps
  · rw [hin] at hv hI
    simp only [List.map_cons, List.map_nil] at hv
    have hI2 : ∀ x, x ∈ gIn C t ↔ (x = i ∨ x = i2) ∧ x < 7 + t := by
      intro x
      rw [hI]
      simp
    rcases hop3 with e | e | e
    · refine fin2 ps T C 0 hI2 ?_ h
      rw [hv, e]
      simp only [eval_and2]
      exact encL_and _ _ ps
    · refine fin2 ps T C 1 hI2 ?_ h
      rw [hv, e]
      simp only [eval_or2]
      exact encL_or _ _ ps
    · refine fin2 ps T C 2 hI2 ?_ h
      rw [hv, e]
      simp only [eval_not_cons]
      exact encL_not _ ps
  · rw [hin] at hlen
    simp at hlen

theorem run_need (ps : List (Fin 7 → Bool)) (T : ℕ) (C : Circuit)
    (hF : PEqualNP.MetaComplexity.FanInTwo C) (hT : val ps C C.output = T) :
    ∀ d, d ≤ C.gates.length → Run T (encL (fun _ => true) ps) d (St ps C d)
  | 0, _ => by
    have : St ps C 0 = [T] := by
      simp [St, need, hT]
    rw [this]
    exact Run.done 0
  | d + 1, hd => by
    have ih := run_need ps T C hF hT d (by omega)
    have ht : C.gates.length - (d + 1) < C.gates.length := by omega
    have hg := List.getElem?_eq_getElem ht
    unfold St need
    split
    · rename_i hin
      set t := C.gates.length - (d + 1)
      have p : (need C d).toList.Perm ((7 + t) :: ((need C d).erase (7 + t)).toList) := by
        conv_lhs => rw [← Finset.insert_erase hin]
        exact Finset.toList_insert (Finset.notMem_erase _ _)
      have h1 : Run T (encL (fun _ => true) ps) d
          (val ps C (7 + t) :: ((need C d).erase (7 + t)).toList.map (val ps C)) := by
        have := Run.perm (p.map (val ps C)) ih
        simpa using this
      exact gate_step ps T C hF hg h1
    · exact Run.mono ih

theorem reduce (ps : List (Fin 7 → Bool)) (f : (Fin 7 → Bool) → Bool) (x0 : Fin 7 → Bool)
    (hx0 : f x0 = true) (C : Circuit) (hC : PEqualNP.MetaComplexity.FanInTwo C)
    (hf : ∀ x, C.eval (List.ofFn x) = f x) :
    ∃ S : List ℕ, S.Sublist ((List.range 7).map (Xv ps)) ∧
      Run (encL f ps) (encL (fun _ => true) ps) C.gates.length S := by
  have hev : ∀ x, C.eval (List.ofFn x) = W C C.output x := fun x => rfl
  have ho : C.output < 7 + C.gates.length := by
    by_contra hc
    have h1 := hf x0
    rw [hx0, hev, W, List.getD_eq_default _ _ (by rw [wires_len, List.length_ofFn]; omega)] at h1
    cases h1
  have hT : val ps C C.output = encL f ps := by
    unfold val
    congr 1
    funext x
    rw [← hev]
    exact hf x
  have hrun := run_need ps (encL f ps) C hC hT C.gates.length le_rfl
  have hb := need_bound C ho C.gates.length le_rfl
  let S := (List.range 7).filter (fun i => decide (i ∈ need C C.gates.length))
  have p : (need C C.gates.length).toList.Perm S := by
    apply toL_perm (List.Nodup.filter _ List.nodup_range)
    intro w
    constructor
    · intro hw
      have := hb w hw
      exact List.mem_filter.2 ⟨List.mem_range.2 (by omega), decide_eq_true hw⟩
    · intro hw
      exact of_decide_eq_true (List.mem_filter.1 hw).2
  have hmap : S.map (val ps C) = S.map (Xv ps) :=
    List.map_congr_left (fun i hi => val_input ps C i (List.mem_range.1 (List.mem_filter.1 hi).1))
  refine ⟨S.map (Xv ps), (List.filter_sublist).map (Xv ps), ?_⟩
  rw [← hmap]
  exact Run.perm (p.map (val ps C)) hrun


/-! ## Part B (lead): invariant, certificate, main theorem -/

def EL : List (ℕ × ℕ) := [(0, 1), (0, 2), (2, 1), (0, 3), (3, 4), (4, 5), (5, 6), (6, 1)]

def fE (x : Fin 7 → Bool) : Bool :=
  decide (∃ u v : Fin 7, (u.val, v.val) ∈ EL ∧ x u = true ∧ x v = true)

def pts : List (Fin 7 → Bool) := (List.range 128).map fun k => fun i => k.testBit i.val

def AA : ℕ := 340282366920938463463374607431768211455

def TT : ℕ := 0xffffffffffeceeecffffeae8ffe8eae8
def XX : List ℕ := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 0xcccccccccccccccccccccccccccccccc, 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00ff00ff00ff00ff00, 0xffff0000ffff0000ffff0000ffff0000, 0xffffffff00000000ffffffff00000000, 0xffffffffffffffff0000000000000000]
def FP : List ℕ := [18, 33, 42, 44, 76, 81, 84]
def SG : List ℕ := [0, 2, 1, 3, 4, 6, 5, 7, 64, 66, 65, 67, 68, 70, 69, 71, 32, 34, 33, 35, 36, 38, 37, 39, 96, 98, 97, 99, 100, 102, 101, 103, 16, 18, 17, 19, 20, 22, 21, 23, 80, 82, 81, 83, 84, 86, 85, 87, 48, 50, 49, 51, 52, 54, 53, 55, 112, 114, 113, 115, 116, 118, 117, 119, 8, 10, 9, 11, 12, 14, 13, 15, 72, 74, 73, 75, 76, 78, 77, 79, 40, 42, 41, 43, 44, 46, 45, 47, 104, 106, 105, 107, 108, 110, 109, 111, 24, 26, 25, 27, 28, 30, 29, 31, 88, 90, 89, 91, 92, 94, 93, 95, 56, 58, 57, 59, 60, 62, 61, 63, 120, 122, 121, 123, 124, 126, 125, 127]


theorem AA_eq : AA = 2 ^ 128 - 1 := by decide

theorem AA_bit {k : ℕ} (hk : k < 128) : AA.testBit k = true := by
  rw [AA_eq, Nat.testBit_two_pow_sub_one]
  simpa using hk

theorem TT_lt : TT < 2 ^ 128 := by decide

theorem TT_bit {k : ℕ} (h : TT.testBit k = true) : k < 128 := by
  by_contra hk
  rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le TT_lt (Nat.pow_le_pow_right (by norm_num) (by omega)))] at h
  cases h

def opb : Fin 4 → Bool → Bool → Bool
  | 0, x, y => x && y
  | 1, x, y => x || y
  | 2, x, _ => !x
  | 3, _, y => !y

theorem opv_bit (o : Fin 4) (a b : ℕ) {k : ℕ} (hk : k < 128) :
    (opv AA o a b).testBit k = opb o (a.testBit k) (b.testBit k) := by
  have hA := AA_bit hk
  fin_cases o <;> simp [opv, opb, Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor, hA]

theorem xor_bit (a : ℕ) {k : ℕ} (hk : k < 128) : (AA ^^^ a).testBit k = !a.testBit k := by
  simp [Nat.testBit_xor, AA_bit hk]

theorem opb_diff : ∀ (o : Fin 4) (x1 y1 x2 y2 : Bool), opb o x1 y1 ≠ opb o x2 y2 → x1 ≠ x2 ∨ y1 ≠ y2 := by
  decide

/-! ### Separation -/

def Cov (L : List ℕ) : Prop :=
  ∀ t u, t < 128 → u < 128 → TT.testBit t = true → TT.testBit u = false →
    ∃ v ∈ L, v.testBit t ≠ v.testBit u

theorem Cov.perm {L₁ L₂ : List ℕ} (p : L₁.Perm L₂) (h : Cov L₁) : Cov L₂ := by
  intro t u ht hu h1 h2
  obtain ⟨v, hv, hne⟩ := h t u ht hu h1 h2
  exact ⟨v, p.subset hv, hne⟩

def sepm (u : ℕ) : List ℕ → ℕ
  | [] => 0
  | v :: vs => (if v.testBit u then AA ^^^ v else v) ||| sepm u vs

theorem sepm_bit (u t : ℕ) (ht : t < 128) : ∀ L : List ℕ, (∃ v ∈ L, v.testBit t ≠ v.testBit u) →
    (sepm u L).testBit t = true
  | [], ⟨v, hv, _⟩ => by simp at hv
  | x :: xs, ⟨v, hv, hne⟩ => by
    unfold sepm
    rw [Nat.testBit_or]
    rcases List.mem_cons.1 hv with rfl | hv
    · split
      · rename_i hu
        rw [xor_bit _ ht]
        rw [hu] at hne
        simp [hne]
      · rename_i hu
        simp only [Bool.not_eq_true] at hu
        rw [hu] at hne
        simp only [ne_eq, Bool.not_eq_false] at hne
        simp [hne]
    · rw [sepm_bit u t ht xs ⟨v, hv, hne⟩, Bool.or_true]

def covB (L : List ℕ) : Bool := FP.all fun u => (sepm u L &&& TT) == TT

theorem fp_ok : ∀ u ∈ FP, u < 128 ∧ TT.testBit u = false := by decide

theorem covB_of_cov {L : List ℕ} (h : Cov L) : covB L = true := by
  unfold covB
  rw [List.all_eq_true]
  intro u hu
  obtain ⟨hu1, hu2⟩ := fp_ok u hu
  rw [beq_iff_eq]
  apply Nat.eq_of_testBit_eq
  intro t
  rw [Nat.testBit_and]
  cases htt : TT.testBit t
  · simp
  · have ht := TT_bit htt
    rw [sepm_bit u t ht L (h t u ht hu1 htt hu2)]
    rfl

/-! ### The read-once witness invariant for tight states -/

def d4 (a1 b1 a2 b2 a3 b3 a4 b4 : Bool) : Bool :=
  !(a1 == a2 && b1 == b2) && !(a1 == a3 && b1 == b3) && !(a1 == a4 && b1 == b4) &&
  !(a2 == a3 && b2 == b3) && !(a2 == a4 && b2 == b4) && !(a3 == a4 && b3 == b4)

theorem d4_swap : ∀ a1 b1 a2 b2 a3 b3 a4 b4 : Bool,
    d4 a1 b1 a2 b2 a3 b3 a4 b4 = d4 b1 a1 b2 a2 b3 a3 b4 a4 := by decide

def piB (o : Fin 4) (x : Bool) : Bool := if o = 2 then !x else x

theorem key1 : ∀ (o : Fin 4) (a1 b1 a2 b2 a3 b3 a4 b4 : Bool), d4 a1 b1 a2 b2 a3 b3 a4 b4 = true →
    opb o a1 b1 ≠ opb o a2 b2 → opb o a1 b1 ≠ opb o a3 b3 → opb o a1 b1 ≠ opb o a4 b4 →
    (o = 0 ∧ a1 = true ∧ b1 = true) ∨ (o = 1 ∧ a1 = false ∧ b1 = false) := by decide

theorem key2 : ∀ (o : Fin 4) (β a1 b1 a2 b2 a3 b3 a4 b4 : Bool), d4 a1 b1 a2 b2 a3 b3 a4 b4 = true →
    (opb o a1 β ≠ opb o a2 β ∨ b1 ≠ b2) → (opb o a1 β ≠ opb o a3 β ∨ b1 ≠ b3) →
    (opb o a1 β ≠ opb o a4 β ∨ b1 ≠ b4) →
    d4 (opb o a1 β) b1 (opb o a2 β) b2 (opb o a3 β) b3 (opb o a4 β) b4 = true ∧
    opb o a1 β = piB o a1 := by decide

theorem piB_ne : ∀ (o : Fin 4) (x y z w : Bool), (piB o x != piB o y || z != w) = (x != y || z != w) := by
  decide

def cst (r : List ℕ) (p1 p2 p3 p4 : ℕ) : Prop :=
  ∀ v ∈ r, v.testBit p2 = v.testBit p1 ∧ v.testBit p3 = v.testBit p1 ∧ v.testBit p4 = v.testBit p1

def BadAt (a b : ℕ) (r : List ℕ) (p1 p2 p3 p4 q1 q2 q3 q4 : ℕ) : Prop :=
  (p1 < 128 ∧ p2 < 128 ∧ p3 < 128 ∧ p4 < 128 ∧ q1 < 128 ∧ q2 < 128 ∧ q3 < 128 ∧ q4 < 128) ∧
  cst r p1 p2 p3 p4 ∧ cst r q1 q2 q3 q4 ∧
  d4 (a.testBit p1) (b.testBit p1) (a.testBit p2) (b.testBit p2) (a.testBit p3) (b.testBit p3)
    (a.testBit p4) (b.testBit p4) = true ∧
  d4 (a.testBit q1) (b.testBit q1) (a.testBit q2) (b.testBit q2) (a.testBit q3) (b.testBit q3)
    (a.testBit q4) (b.testBit q4) = true ∧
  (TT.testBit p1 = true ∧ TT.testBit p2 = false ∧ TT.testBit p3 = false ∧ TT.testBit p4 = false) ∧
  (TT.testBit q1 = false ∧ TT.testBit q2 = true ∧ TT.testBit q3 = true ∧ TT.testBit q4 = true) ∧
  (a.testBit p1 != a.testBit q1 || b.testBit p1 != b.testBit q1) = true

def Bad (a b : ℕ) (r : List ℕ) : Prop :=
  ∃ p1 p2 p3 p4 q1 q2 q3 q4 : ℕ, BadAt a b r p1 p2 p3 p4 q1 q2 q3 q4

def ROk (L : List ℕ) : Prop := ∀ a b r, L.Perm (a :: b :: r) → ¬ Bad a b r

theorem cst_sub {r r' : List ℕ} (hs : ∀ v ∈ r', v ∈ r) {p1 p2 p3 p4 : ℕ} (h : cst r p1 p2 p3 p4) :
    cst r' p1 p2 p3 p4 := fun v hv => h v (hs v hv)

theorem Bad.sub {a b : ℕ} {r r' : List ℕ} (hs : ∀ v ∈ r', v ∈ r) (h : Bad a b r) : Bad a b r' := by
  obtain ⟨p1, p2, p3, p4, q1, q2, q3, q4, hl, cP, cQ, h3⟩ := h
  exact ⟨p1, p2, p3, p4, q1, q2, q3, q4, hl, cst_sub hs cP, cst_sub hs cQ, h3⟩

theorem Bad.swap {a b : ℕ} {r : List ℕ} (h : Bad a b r) : Bad b a r := by
  obtain ⟨p1, p2, p3, p4, q1, q2, q3, q4, hl, cP, cQ, dP, dQ, tP, tQ, hx⟩ := h
  refine ⟨p1, p2, p3, p4, q1, q2, q3, q4, hl, cP, cQ, ?_, ?_, tP, tQ, ?_⟩
  · rw [← d4_swap]; exact dP
  · rw [← d4_swap]; exact dQ
  · rw [Bool.or_comm]; exact hx

theorem gate_diff {o : Fin 4} {a b : ℕ} {r : List ℕ} (hc : Cov (opv AA o a b :: r)) {t u : ℕ}
    (ht : t < 128) (hu : u < 128) (htt : TT.testBit t = true) (huu : TT.testBit u = false)
    (hcu : ∀ v ∈ r, v.testBit t = v.testBit u) :
    opb o (a.testBit t) (b.testBit t) ≠ opb o (a.testBit u) (b.testBit u) := by
  obtain ⟨v, hv, hne⟩ := hc t u ht hu htt huu
  rcases List.mem_cons.1 hv with rfl | hv
  · rwa [opv_bit _ _ _ ht, opv_bit _ _ _ hu] at hne
  · exact absurd (hcu v hv) hne

theorem bad_gate (o : Fin 4) {a b : ℕ} {r : List ℕ} (hc : Cov (opv AA o a b :: r)) (h : Bad a b r) :
    False := by
  obtain ⟨p1, p2, p3, p4, q1, q2, q3, q4, ⟨l1, l2, l3, l4, l5, l6, l7, l8⟩, cP, cQ, dP, dQ,
    ⟨t1, t2, t3, t4⟩, ⟨u1, u2, u3, u4⟩, hx⟩ := h
  have e2 := gate_diff hc l1 l2 t1 t2 (fun v hv => (cP v hv).1.symm)
  have e3 := gate_diff hc l1 l3 t1 t3 (fun v hv => (cP v hv).2.1.symm)
  have e4 := gate_diff hc l1 l4 t1 t4 (fun v hv => (cP v hv).2.2.symm)
  have f2 := gate_diff hc l6 l5 u2 u1 (fun v hv => (cQ v hv).1)
  have f3 := gate_diff hc l7 l5 u3 u1 (fun v hv => (cQ v hv).2.1)
  have f4 := gate_diff hc l8 l5 u4 u1 (fun v hv => (cQ v hv).2.2)
  have k1 := key1 o _ _ _ _ _ _ _ _ dP e2 e3 e4
  have k2 := key1 o _ _ _ _ _ _ _ _ dQ (Ne.symm f2) (Ne.symm f3) (Ne.symm f4)
  rcases k1 with ⟨ho, ha, hb⟩ | ⟨ho, ha, hb⟩ <;> rcases k2 with ⟨ho', ha', hb'⟩ | ⟨ho', ha', hb'⟩
  · rw [ha, hb, ha', hb'] at hx; cases hx
  · rw [ho] at ho'; cases ho'
  · rw [ho] at ho'; cases ho'
  · rw [ha, hb, ha', hb'] at hx; cases hx

theorem side_diff {w b : ℕ} {m : List ℕ} (hc : Cov (w :: b :: m)) {t u : ℕ}
    (ht : t < 128) (hu : u < 128) (htt : TT.testBit t = true) (huu : TT.testBit u = false)
    (hcu : ∀ v ∈ m, v.testBit t = v.testBit u) :
    w.testBit t ≠ w.testBit u ∨ b.testBit t ≠ b.testBit u := by
  obtain ⟨v, hv, hne⟩ := hc t u ht hu htt huu
  rcases List.mem_cons.1 hv with rfl | hv
  · exact Or.inl hne
  · rcases List.mem_cons.1 hv with rfl | hv
    · exact Or.inr hne
    · exact absurd (hcu v hv) hne

theorem bad_side (o : Fin 4) {a b b' : ℕ} {m : List ℕ} (hc : Cov (opv AA o a b' :: b :: m))
    (h : Bad a b (b' :: m)) : Bad (opv AA o a b') b m := by
  obtain ⟨p1, p2, p3, p4, q1, q2, q3, q4, ⟨l1, l2, l3, l4, l5, l6, l7, l8⟩, cP, cQ, dP, dQ,
    tP, tQ, hx⟩ := h
  have cP' : cst m p1 p2 p3 p4 := cst_sub (fun v hv => List.mem_cons_of_mem _ hv) cP
  have cQ' : cst m q1 q2 q3 q4 := cst_sub (fun v hv => List.mem_cons_of_mem _ hv) cQ
  obtain ⟨bp2, bp3, bp4⟩ := cP b' (List.mem_cons_self ..)
  obtain ⟨bq2, bq3, bq4⟩ := cQ b' (List.mem_cons_self ..)
  have e2 := side_diff hc l1 l2 tP.1 tP.2.1 (fun v hv => (cP' v hv).1.symm)
  have e3 := side_diff hc l1 l3 tP.1 tP.2.2.1 (fun v hv => (cP' v hv).2.1.symm)
  have e4 := side_diff hc l1 l4 tP.1 tP.2.2.2 (fun v hv => (cP' v hv).2.2.symm)
  have f2 := side_diff hc l6 l5 tQ.2.1 tQ.1 (fun v hv => (cQ' v hv).1)
  have f3 := side_diff hc l7 l5 tQ.2.2.1 tQ.1 (fun v hv => (cQ' v hv).2.1)
  have f4 := side_diff hc l8 l5 tQ.2.2.2 tQ.1 (fun v hv => (cQ' v hv).2.2)
  simp only [opv_bit _ _ _ l1, opv_bit _ _ _ l2, opv_bit _ _ _ l3, opv_bit _ _ _ l4,
    opv_bit _ _ _ l5, opv_bit _ _ _ l6, opv_bit _ _ _ l7, opv_bit _ _ _ l8,
    bp2, bp3, bp4, bq2, bq3, bq4] at e2 e3 e4 f2 f3 f4
  obtain ⟨dP', hP⟩ := key2 o _ _ _ _ _ _ _ _ _ dP e2 e3 e4
  obtain ⟨dQ', hQ⟩ := key2 o _ _ _ _ _ _ _ _ _ dQ (f2.imp Ne.symm Ne.symm) (f3.imp Ne.symm Ne.symm)
    (f4.imp Ne.symm Ne.symm)
  refine ⟨p1, p2, p3, p4, q1, q2, q3, q4, ⟨l1, l2, l3, l4, l5, l6, l7, l8⟩, cP', cQ', ?_, ?_, tP, tQ, ?_⟩
  · simp only [opv_bit _ _ _ l1, opv_bit _ _ _ l2, opv_bit _ _ _ l3, opv_bit _ _ _ l4, bp2, bp3, bp4]
    exact dP'
  · simp only [opv_bit _ _ _ l5, opv_bit _ _ _ l6, opv_bit _ _ _ l7, opv_bit _ _ _ l8, bq2, bq3, bq4]
    exact dQ'
  · rw [opv_bit _ _ _ l1, opv_bit _ _ _ l5, hP, hQ, piB_ne]
    exact hx

theorem bad_far (o : Fin 4) {a b a' b' : ℕ} {m : List ℕ} (h : Bad a b (a' :: b' :: m)) :
    Bad a b (opv AA o a' b' :: m) := by
  obtain ⟨p1, p2, p3, p4, q1, q2, q3, q4, ⟨l1, l2, l3, l4, l5, l6, l7, l8⟩, cP, cQ, h3⟩ := h
  refine ⟨p1, p2, p3, p4, q1, q2, q3, q4, ⟨l1, l2, l3, l4, l5, l6, l7, l8⟩, ?_, ?_, h3⟩
  · intro v hv
    rcases List.mem_cons.1 hv with rfl | hv
    · obtain ⟨x2, x3, x4⟩ := cP a' (by simp)
      obtain ⟨y2, y3, y4⟩ := cP b' (by simp)
      simp only [opv_bit _ _ _ l1, opv_bit _ _ _ l2, opv_bit _ _ _ l3, opv_bit _ _ _ l4,
        x2, x3, x4, y2, y3, y4]
      simp
    · exact cP v (by simp [hv])
  · intro v hv
    rcases List.mem_cons.1 hv with rfl | hv
    · obtain ⟨x2, x3, x4⟩ := cQ a' (by simp)
      obtain ⟨y2, y3, y4⟩ := cQ b' (by simp)
      simp only [opv_bit _ _ _ l5, opv_bit _ _ _ l6, opv_bit _ _ _ l7, opv_bit _ _ _ l8,
        x2, x3, x4, y2, y3, y4]
      simp
    · exact cQ v (by simp [hv])

def swp : Fin 4 → Fin 4
  | 0 => 0
  | 1 => 1
  | 2 => 3
  | 3 => 2

theorem opv_swp (o : Fin 4) (a b : ℕ) : opv AA o a b = opv AA (swp o) b a := by
  fin_cases o
  · exact Nat.land_comm a b
  · exact Nat.lor_comm a b
  · rfl
  · rfl

theorem perm_two {x y : ℕ} {s t : List ℕ} (h : (x :: s).Perm (y :: t)) (hne : x ≠ y) :
    ∃ m, s.Perm (y :: m) ∧ t.Perm (x :: m) := by
  have hy : y ∈ s := by
    have := h.symm.subset (List.mem_cons_self ..)
    rcases List.mem_cons.1 this with e | e
    · exact absurd e.symm hne
    · exact e
  have hs := List.perm_cons_erase hy
  refine ⟨s.erase y, hs, ?_⟩
  have : (y :: x :: s.erase y).Perm (y :: t) :=
    (List.Perm.swap _ _ _).trans ((hs.cons x).symm.trans h)
  exact this.cons_inv.symm

theorem perm_split {x y a b : ℕ} {z r : List ℕ} (h : (x :: y :: z).Perm (a :: b :: r)) :
    (x = a ∧ y = b ∧ z.Perm r) ∨ (x = b ∧ y = a ∧ z.Perm r) ∨
    (∃ m, x = a ∧ z.Perm (b :: m) ∧ r.Perm (y :: m)) ∨
    (∃ m, x = b ∧ z.Perm (a :: m) ∧ r.Perm (y :: m)) ∨
    (∃ m, y = a ∧ z.Perm (b :: m) ∧ r.Perm (x :: m)) ∨
    (∃ m, y = b ∧ z.Perm (a :: m) ∧ r.Perm (x :: m)) ∨
    (∃ m, z.Perm (a :: b :: m) ∧ r.Perm (x :: y :: m)) := by
  by_cases hxa : x = a
  · subst hxa
    have h1 := h.cons_inv
    by_cases hyb : y = b
    · subst hyb
      exact Or.inl ⟨rfl, rfl, h1.cons_inv⟩
    · obtain ⟨m, h2, h3⟩ := perm_two h1 hyb
      exact Or.inr (Or.inr (Or.inl ⟨m, rfl, h2, h3⟩))
  · obtain ⟨m1, h1, h2⟩ := perm_two h hxa
    -- h1 : (y :: z).Perm (a :: m1), h2 : (b :: r).Perm (x :: m1)
    by_cases hya : y = a
    · subst hya
      have h3 := h1.cons_inv
      by_cases hxb : x = b
      · subst hxb
        exact Or.inr (Or.inl ⟨rfl, rfl, h3.trans h2.cons_inv.symm⟩)
      · obtain ⟨m, h4, h5⟩ := perm_two h2 (Ne.symm hxb)
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨m, rfl, h3.trans h5, h4⟩))))
    · obtain ⟨m2, h3, h4⟩ := perm_two h1 hya
      -- h3 : z.Perm (a :: m2), h4 : m1.Perm (y :: m2)
      have h5 : (b :: r).Perm (x :: y :: m2) := h2.trans (h4.cons x)
      by_cases hxb : x = b
      · subst hxb
        exact Or.inr (Or.inr (Or.inr (Or.inl ⟨m2, rfl, h3, h5.cons_inv⟩)))
      · by_cases hyb : y = b
        · subst hyb
          have h6 : (y :: r).Perm (y :: x :: m2) := h5.trans (List.Perm.swap _ _ _)
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨m2, rfl, h3, h6.cons_inv⟩)))))
        · obtain ⟨m3, h6, h7⟩ := perm_two h5 (Ne.symm hxb)
          obtain ⟨m4, h8, h9⟩ := perm_two h7 hyb
          -- h6 : r.Perm (x :: m3), h7 : (y :: m2).Perm (b :: m3), h8 : m2.Perm (b :: m4), h9 : m3.Perm (y :: m4)
          refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨m4, ?_, ?_⟩)))))
          · exact h3.trans (h8.cons a)
          · exact h6.trans (h9.cons x)

theorem rok_two {o : Fin 4} {a b : ℕ} {r : List ℕ} (hc : Cov (opv AA o a b :: r))
    (hr : ROk (opv AA o a b :: r)) : ROk (a :: b :: r) := by
  intro x y z hp hbad
  rcases perm_split hp.symm with ⟨rfl, rfl, hz⟩ | ⟨rfl, rfl, hz⟩ | ⟨m, rfl, hz, hm⟩ |
      ⟨m, rfl, hz, hm⟩ | ⟨m, rfl, hz, hm⟩ | ⟨m, rfl, hz, hm⟩ | ⟨m, hz, hm⟩
  · exact bad_gate o hc (hbad.sub fun v hv => hz.symm.subset hv)
  · rw [opv_swp] at hc
    exact bad_gate (swp o) hc (hbad.sub fun v hv => hz.symm.subset hv)
  · have hc' : Cov (opv AA o x b :: y :: m) := hc.perm (hm.cons _)
    have hb := bad_side o hc' (hbad.sub fun v hv => hz.symm.subset hv)
    exact hr _ _ _ (hm.cons _) hb
  · rw [opv_swp] at hc hr
    have hc' : Cov (opv AA (swp o) x a :: y :: m) := hc.perm (hm.cons _)
    have hb := bad_side (swp o) hc' (hbad.sub fun v hv => hz.symm.subset hv)
    exact hr _ _ _ (hm.cons _) hb
  · have hc' : Cov (opv AA o y b :: x :: m) := hc.perm (hm.cons _)
    have hb := bad_side o hc' ((hbad.sub fun v hv => hz.symm.subset hv).swap)
    exact hr _ _ _ (hm.cons _) hb
  · rw [opv_swp] at hc hr
    have hc' : Cov (opv AA (swp o) y a :: x :: m) := hc.perm (hm.cons _)
    have hb := bad_side (swp o) hc' ((hbad.sub fun v hv => hz.symm.subset hv).swap)
    exact hr _ _ _ (hm.cons _) hb
  · have hb := bad_far o (hbad.sub fun v hv => hz.symm.subset hv)
    refine hr x y (opv AA o a b :: m) ?_ hb
    refine (hm.cons _).trans ?_
    exact (List.Perm.swap _ _ _).trans ((List.Perm.swap _ _ _).cons _)

/-! ### Invariants of runs -/

theorem len_kept (k : Bool) (x : ℕ) (xs : List ℕ) : xs.length ≤ (kept k x xs).length := by
  cases k <;> simp [kept]

theorem cov_TT : Cov [TT] := fun t u _ _ h1 h2 => ⟨TT, by simp, by rw [h1, h2]; simp⟩

theorem Run.inv {s : ℕ} {L : List ℕ} (h : Run TT AA s L) :
    L.length ≤ s + 1 ∧ Cov L ∧ (L.length = s + 1 → ROk L) := by
  induction h with
  | done s =>
    refine ⟨by simp, cov_TT, fun _ a b r hp _ => ?_⟩
    have := hp.length_eq
    simp at this
  | perm p _ ih =>
    refine ⟨p.length_eq ▸ ih.1, ih.2.1.perm p, fun hl a b r hp => ?_⟩
    exact ih.2.2 (p.length_eq ▸ hl) a b r (p.trans hp)
  | mono _ ih =>
    exact ⟨by omega, ih.2.1, fun hl => absurd hl (by omega)⟩
  | @two s a b r o ka kb _ ih =>
    obtain ⟨hl, hc, hro⟩ := ih
    have h1 := len_kept ka a (kept kb b r)
    have h2 := len_kept kb b r
    simp only [List.length_cons] at hl
    refine ⟨by simp only [List.length_cons]; omega, ?_, ?_⟩
    · intro t u ht hu h1 h2
      obtain ⟨v, hv, hne⟩ := hc t u ht hu h1 h2
      rcases List.mem_cons.1 hv with rfl | hv
      · rw [opv_bit _ _ _ ht, opv_bit _ _ _ hu] at hne
        rcases opb_diff _ _ _ _ _ hne with e | e
        · exact ⟨a, by simp, e⟩
        · exact ⟨b, by simp, e⟩
      · rcases mem_kept hv with rfl | hv
        · exact ⟨v, by simp, hne⟩
        · rcases mem_kept hv with rfl | hv
          · exact ⟨v, by simp, hne⟩
          · exact ⟨v, by simp [hv], hne⟩
    · intro hlen
      simp only [List.length_cons] at hlen
      cases ka <;> cases kb
      · exact rok_two hc (hro (by simp [kept]; omega))
      · simp [kept] at hl; omega
      · simp [kept] at hl; omega
      · simp [kept] at hl; omega
  | @one s a w r ka hw _ ih =>
    obtain ⟨hl, hc, _⟩ := ih
    have h1 := len_kept ka a r
    simp only [List.length_cons] at hl
    refine ⟨by simp only [List.length_cons]; omega, ?_, fun hlen => by simp at hlen; omega⟩
    intro t u ht hu h1 h2
    obtain ⟨v, hv, hne⟩ := hc t u ht hu h1 h2
    rcases List.mem_cons.1 hv with rfl | hv
    · rcases hw with rfl | rfl | rfl | rfl
      · exact ⟨v, by simp, hne⟩
      · rw [xor_bit _ ht, xor_bit _ hu] at hne
        exact ⟨a, by simp, fun e => hne (by rw [e])⟩
      · simp at hne
      · rw [AA_bit ht, AA_bit hu] at hne
        exact absurd rfl hne
    · rcases mem_kept hv with rfl | hv
      · exact ⟨v, by simp, hne⟩
      · exact ⟨v, by simp [hv], hne⟩
  | @const s w r hw _ ih =>
    obtain ⟨hl, hc, _⟩ := ih
    simp only [List.length_cons] at hl
    refine ⟨by omega, ?_, fun hlen => by omega⟩
    intro t u ht hu h1 h2
    obtain ⟨v, hv, hne⟩ := hc t u ht hu h1 h2
    rcases List.mem_cons.1 hv with rfl | hv
    · rcases hw with rfl | rfl
      · simp at hne
      · rw [AA_bit ht, AA_bit hu] at hne
        exact absurd rfl hne
    · exact ⟨v, hv, hne⟩

/-! ### Witnesses -/

structure Wt where
  xi : ℕ
  xj : ℕ
  nxi : ℕ
  nxj : ℕ
  m1 : ℕ
  m2 : ℕ
  p1 : ℕ
  p2 : ℕ
  p3 : ℕ
  p4 : ℕ
  q1 : ℕ
  q2 : ℕ
  q3 : ℕ
  q4 : ℕ

def WL : List Wt := [⟨0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 0xcccccccccccccccccccccccccccccccc, 0x55555555555555555555555555555555, 0x33333333333333333333333333333333, 0xf, 0xf0, 3, 0, 1, 2, 4, 5, 6, 7⟩,
  ⟨0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0, 0x55555555555555555555555555555555, 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f, 0x33, 0xcc, 5, 0, 1, 4, 2, 3, 6, 7⟩,
  ⟨0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0, 0xcccccccccccccccccccccccccccccccc, 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f, 0x33333333333333333333333333333333, 0x55, 0xaa, 6, 0, 2, 4, 1, 3, 5, 7⟩,
  ⟨0xff00ff00ff00ff00ff00ff00ff00ff00, 0xffff0000ffff0000ffff0000ffff0000, 0xff00ff00ff00ff00ff00ff00ff00ff, 0xffff0000ffff0000ffff0000ffff, 0x1010101, 0x202020200000000, 24, 0, 8, 16, 33, 41, 49, 57⟩,
  ⟨0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 0xcccccccccccccccccccccccccccccccc, 0x55555555555555555555555555555555, 0x33333333333333333333333333333333, 0xf, 0xf000000000000000000, 3, 0, 1, 2, 72, 73, 74, 75⟩,
  ⟨0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 0xff00ff00ff00ff00ff00ff00ff00ff00, 0x55555555555555555555555555555555, 0xff00ff00ff00ff00ff00ff00ff00ff, 0x303, 0xc0c0000, 9, 0, 1, 8, 18, 19, 26, 27⟩,
  ⟨0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 0xff00ff00ff00ff00ff00ff00ff00ff00, 0x55555555555555555555555555555555, 0xff00ff00ff00ff00ff00ff00ff00ff, 0x303, 0x30300000, 9, 0, 1, 8, 20, 21, 28, 29⟩,
  ⟨0xffff0000ffff0000ffff0000ffff0000, 0xffffffff00000000ffffffff00000000, 0xffff0000ffff0000ffff0000ffff, 0xffffffff00000000ffffffff, 0x1000100010001, 0x1000100010001000000000000000000, 48, 0, 16, 32, 72, 88, 104, 120⟩,
  ⟨0xffffffff00000000ffffffff00000000, 0xffffffffffffffff0000000000000000, 0xffffffff00000000ffffffff, 0xffffffffffffffff, 0x1000000010000000100000001, 0x40000000400000004000000040000, 96, 0, 32, 64, 18, 50, 82, 114⟩,
  ⟨0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 0xcccccccccccccccccccccccccccccccc, 0x55555555555555555555555555555555, 0x33333333333333333333333333333333, 0xf, 0xf00000000000000000, 3, 0, 1, 2, 68, 69, 70, 71⟩,
  ⟨0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0, 0xcccccccccccccccccccccccccccccccc, 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f, 0x33333333333333333333333333333333, 0x55, 0xaa0000000000000000, 6, 0, 2, 4, 65, 67, 69, 71⟩,
  ⟨0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 0xcccccccccccccccccccccccccccccccc, 0x55555555555555555555555555555555, 0x33333333333333333333333333333333, 0xf, 0xf000, 3, 0, 1, 2, 12, 13, 14, 15⟩,
  ⟨0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0, 0x55555555555555555555555555555555, 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f, 0x33, 0xcc00, 5, 0, 1, 4, 10, 11, 14, 15⟩,
  ⟨0xffffffffffffffff0000000000000000, 0xcccccccccccccccccccccccccccccccc, 0xffffffffffffffff, 0x33333333333333333333333333333333, 0x50000000000000005, 0xa000000000000000a00000000, 66, 0, 2, 64, 33, 35, 97, 99⟩,
  ⟨0xffffffffffffffff0000000000000000, 0xcccccccccccccccccccccccccccccccc, 0xffffffffffffffff, 0x33333333333333333333333333333333, 0x50000000000000005, 0x50000000000000005000000000, 66, 0, 2, 64, 36, 38, 100, 102⟩]


def cm (v m : ℕ) : Bool := (v &&& m == 0) || (v &&& m == m)

def wgood (w : Wt) (a b : ℕ) : Bool :=
  decide (w.p1 < 128 ∧ w.p2 < 128 ∧ w.p3 < 128 ∧ w.p4 < 128 ∧ w.q1 < 128 ∧ w.q2 < 128 ∧
    w.q3 < 128 ∧ w.q4 < 128) &&
  (w.m1.testBit w.p1 && w.m1.testBit w.p2 && w.m1.testBit w.p3 && w.m1.testBit w.p4) &&
  (w.m2.testBit w.q1 && w.m2.testBit w.q2 && w.m2.testBit w.q3 && w.m2.testBit w.q4) &&
  d4 (a.testBit w.p1) (b.testBit w.p1) (a.testBit w.p2) (b.testBit w.p2) (a.testBit w.p3)
    (b.testBit w.p3) (a.testBit w.p4) (b.testBit w.p4) &&
  d4 (a.testBit w.q1) (b.testBit w.q1) (a.testBit w.q2) (b.testBit w.q2) (a.testBit w.q3)
    (b.testBit w.q3) (a.testBit w.q4) (b.testBit w.q4) &&
  (TT.testBit w.p1 && !TT.testBit w.p2 && !TT.testBit w.p3 && !TT.testBit w.p4) &&
  (!TT.testBit w.q1 && TT.testBit w.q2 && TT.testBit w.q3 && TT.testBit w.q4) &&
  (a.testBit w.p1 != a.testBit w.q1 || b.testBit w.p1 != b.testBit w.q1) && (a != b)

set_option maxHeartbeats 4000000 in
theorem wl_good : ∀ w ∈ WL, ∀ a ∈ [w.xi, w.nxi], ∀ b ∈ [w.xj, w.nxj],
    wgood w a b = true := by decide +kernel

theorem cm_eq {v m p q : ℕ} (h : cm v m = true) (hp : m.testBit p = true) (hq : m.testBit q = true) :
    v.testBit q = v.testBit p := by
  unfold cm at h
  rw [Bool.or_eq_true, beq_iff_eq, beq_iff_eq] at h
  have ep : (v &&& m).testBit p = v.testBit p := by rw [Nat.testBit_and, hp, Bool.and_true]
  have eq : (v &&& m).testBit q = v.testBit q := by rw [Nat.testBit_and, hq, Bool.and_true]
  rcases h with h | h
  · rw [← ep, ← eq, h]; simp
  · rw [← ep, ← eq, h, hp, hq]


/-! ### Trees, sorting, children -/

def picks : List ℕ → List (ℕ × List ℕ)
  | [] => []
  | x :: xs => (x, xs) :: (picks xs).map fun q => (q.1, x :: q.2)

def pairsOf : List ℕ → List (ℕ × ℕ × List ℕ)
  | [] => []
  | x :: xs => (picks xs).map (fun q => (x, q.1, q.2)) ++
      (pairsOf xs).map fun q => (q.1, q.2.1, x :: q.2.2)

def wone (w : Wt) (L : List ℕ) (a b : ℕ) : Bool :=
  L.count a == 1 && L.count b == 1 && L.all (fun v => v == a || v == b || (cm v w.m1 && cm v w.m2))

def wtry (w : Wt) (L : List ℕ) : Bool :=
  wone w L w.xi w.xj || wone w L w.xi w.nxj || wone w L w.nxi w.xj || wone w L w.nxi w.nxj

def wit (L : List ℕ) : Bool := WL.any fun w => wtry w L

def passes (s : ℕ) (L : List ℕ) : Bool :=
  Nat.ble L.length (s + 1) && !(L.length == s + 1 && wit L) && covB L

def twoCh (a b : ℕ) (r : List ℕ) : List (List ℕ) :=
  ([0, 1, 2, 3] : List (Fin 4)).flatMap fun o => [true, false].flatMap fun ka =>
    [true, false].map fun kb => opv AA o a b :: kept ka a (kept kb b r)

def children (L : List ℕ) : List (List ℕ) :=
  (pairsOf L).flatMap (fun q => twoCh q.1 q.2.1 q.2.2) ++
  (picks L).flatMap (fun q => [q.1 :: q.1 :: q.2, (AA ^^^ q.1) :: q.1 :: q.2, (AA ^^^ q.1) :: q.2,
    0 :: q.1 :: q.2, 0 :: q.2, AA :: q.1 :: q.2, AA :: q.2]) ++
  [0 :: L, AA :: L]

inductive Tr where
  | E : Tr
  | N : Tr → List ℕ → ℕ → Tr → Tr

def cmpL : List ℕ → List ℕ → Ordering
  | [], [] => Ordering.eq
  | [], _ :: _ => Ordering.lt
  | _ :: _, [] => Ordering.gt
  | a :: as, b :: bs => if Nat.blt a b then Ordering.lt else if Nat.blt b a then Ordering.gt else cmpL as bs

def look : Tr → List ℕ → ℕ → Bool
  | Tr.E, _, _ => false
  | Tr.N l k v r, x, s =>
    match cmpL x k with
    | Ordering.lt => look l x s
    | Ordering.gt => look r x s
    | Ordering.eq => Nat.ble s v

def srt (L : List ℕ) : List ℕ := List.insertionSort (fun a b => a ≤ b) L

def pg : List ℕ → ℕ → ℕ
  | [], _ => 0
  | q :: qs, v => Nat.bit (v.testBit q) (pg qs v)

def lookS (t : Tr) (s : ℕ) (L : List ℕ) : Bool :=
  look t (srt L) s || look t (srt (L.map (pg SG))) s

def chkE (t : Tr) (K : List ℕ) (lev : ℕ) : Bool :=
  Nat.ble 1 lev && !(cmpL K [TT] == Ordering.eq) &&
    (children K).all fun ch => !(passes (lev - 1) ch) || lookS t (lev - 1) ch

def allE (t : Tr) : Tr → Bool
  | Tr.E => true
  | Tr.N l k v r => chkE t k v && allE t l && allE t r


theorem srt_perm {L₁ L₂ : List ℕ} (p : L₁.Perm L₂) : srt L₁ = srt L₂ := by
  apply List.Perm.eq_of_sortedLE
  · exact List.sortedLE_iff_pairwise.2 (List.pairwise_insertionSort _ _)
  · exact List.sortedLE_iff_pairwise.2 (List.pairwise_insertionSort _ _)
  · exact ((List.perm_insertionSort _ L₁).trans p).trans (List.perm_insertionSort _ L₂).symm

theorem srt_perm_self (L : List ℕ) : (srt L).Perm L := List.perm_insertionSort _ L

inductive Mem : Tr → List ℕ → ℕ → Prop
  | here (l : Tr) (k : List ℕ) (v : ℕ) (r : Tr) : Mem (Tr.N l k v r) k v
  | left {l : Tr} {k k' : List ℕ} {v v' : ℕ} (r : Tr) : Mem l k' v' → Mem (Tr.N l k v r) k' v'
  | right (l : Tr) {r : Tr} {k k' : List ℕ} {v v' : ℕ} : Mem r k' v' → Mem (Tr.N l k v r) k' v'

theorem cmpL_eq : ∀ {a b : List ℕ}, cmpL a b = Ordering.eq → a = b
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [cmpL] at h
  | _ :: _, [], h => by simp [cmpL] at h
  | x :: xs, y :: ys, h => by
    unfold cmpL at h
    by_cases h1 : Nat.blt x y = true
    · rw [if_pos h1] at h; cases h
    · rw [if_neg h1] at h
      by_cases h2 : Nat.blt y x = true
      · rw [if_pos h2] at h; cases h
      · rw [if_neg h2] at h
        rw [Nat.blt_eq] at h1 h2
        rw [cmpL_eq h, show x = y by omega]

theorem look_sound : ∀ {t : Tr} {x : List ℕ} {s : ℕ}, look t x s = true → ∃ v, Mem t x v ∧ s ≤ v
  | Tr.E, _, _, h => by simp [look] at h
  | Tr.N l k v r, x, s, h => by
    unfold look at h
    split at h
    · obtain ⟨w, hw, hs⟩ := look_sound h
      exact ⟨w, Mem.left r hw, hs⟩
    · obtain ⟨w, hw, hs⟩ := look_sound h
      exact ⟨w, Mem.right l hw, hs⟩
    · rename_i hc
      rw [cmpL_eq hc]
      exact ⟨v, Mem.here l k v r, Nat.le_of_ble_eq_true h⟩

theorem allE_sound (t : Tr) : ∀ {t' : Tr} {K : List ℕ} {v : ℕ}, allE t t' = true → Mem t' K v →
    chkE t K v = true
  | Tr.E, _, _, _, hm => by cases hm
  | Tr.N l k w r, K, v, h, hm => by
    unfold allE at h
    simp only [Bool.and_eq_true] at h
    cases hm with
    | here => exact h.1.1
    | left _ hm => exact allE_sound t h.1.2 hm
    | right _ hm => exact allE_sound t h.2 hm

theorem picks_sound : ∀ {L : List ℕ} {x : ℕ} {r : List ℕ}, (x, r) ∈ picks L → L.Perm (x :: r)
  | [], _, _, h => by simp [picks] at h
  | y :: ys, x, r, h => by
    simp only [picks, List.mem_cons, Prod.mk.injEq, List.mem_map] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨⟨a, b⟩, hq, he⟩
    · exact List.Perm.refl _
    · simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact ((picks_sound hq).cons y).trans (List.Perm.swap _ _ _)

theorem picks_complete : ∀ {L : List ℕ} {x : ℕ}, x ∈ L → ∃ r, (x, r) ∈ picks L
  | [], _, h => by simp at h
  | y :: ys, x, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact ⟨ys, by simp [picks]⟩
    · obtain ⟨r, hr⟩ := picks_complete h
      exact ⟨y :: r, by simp only [picks, List.mem_cons, List.mem_map]; exact Or.inr ⟨(x, r), hr, rfl⟩⟩

theorem pick_perm {L r : List ℕ} {x : ℕ} (hL : L.Perm (x :: r)) :
    ∃ r', (x, r') ∈ picks L ∧ r'.Perm r := by
  obtain ⟨r', hr'⟩ := picks_complete (hL.symm.subset (List.mem_cons_self ..))
  exact ⟨r', hr', ((picks_sound hr').symm.trans hL).cons_inv⟩

theorem pairs_complete : ∀ {K : List ℕ} {a b : ℕ} {r : List ℕ}, K.Perm (a :: b :: r) →
    ∃ q ∈ pairsOf K, ((q.1 = a ∧ q.2.1 = b) ∨ (q.1 = b ∧ q.2.1 = a)) ∧ q.2.2.Perm r
  | [], _, _, _, h => by have := h.length_eq; simp at this
  | x :: xs, a, b, r, h => by
    by_cases hxa : x = a
    · subst hxa
      have h1 : xs.Perm (b :: r) := h.cons_inv
      obtain ⟨r', hr', hp⟩ := pick_perm h1
      exact ⟨(x, b, r'), by simp only [pairsOf, List.mem_append, List.mem_map]; exact Or.inl ⟨(b, r'), hr', rfl⟩,
        Or.inl ⟨rfl, rfl⟩, hp⟩
    · by_cases hxb : x = b
      · subst hxb
        have h1 : xs.Perm (a :: r) := (h.trans (List.Perm.swap _ _ _)).cons_inv
        obtain ⟨r', hr', hp⟩ := pick_perm h1
        exact ⟨(x, a, r'), by simp only [pairsOf, List.mem_append, List.mem_map]; exact Or.inl ⟨(a, r'), hr', rfl⟩,
          Or.inr ⟨rfl, rfl⟩, hp⟩
      · have hxr : x ∈ r := by
          have := h.subset (List.mem_cons_self ..)
          simp only [List.mem_cons] at this
          rcases this with h' | h' | h'
          · exact absurd h' hxa
          · exact absurd h' hxb
          · exact h'
        have hr := List.perm_cons_erase hxr
        have h2 : xs.Perm (a :: b :: r.erase x) := by
          apply List.Perm.cons_inv (a := x)
          refine h.trans ?_
          refine ((hr.cons b).cons a).trans ?_
          exact ((List.Perm.swap _ _ _).cons a).trans (List.Perm.swap _ _ _)
        obtain ⟨q, hq, hab, hp⟩ := pairs_complete h2
        refine ⟨(q.1, q.2.1, x :: q.2.2), ?_, hab, ?_⟩
        · simp only [pairsOf, List.mem_append, List.mem_map]
          exact Or.inr ⟨q, hq, rfl⟩
        · exact (hp.cons x).trans hr.symm

theorem kept_swap (ka kb : Bool) (a b : ℕ) (r : List ℕ) :
    (kept ka a (kept kb b r)).Perm (kept kb b (kept ka a r)) := by
  cases ka <;> cases kb <;> simp [kept] <;> exact List.Perm.swap _ _ _

theorem kept_perm (k : Bool) (x : ℕ) {l₁ l₂ : List ℕ} (p : l₁.Perm l₂) :
    (kept k x l₁).Perm (kept k x l₂) := by
  cases k
  · exact p
  · exact p.cons x


theorem pairsOf_sound : ∀ {L : List ℕ} {q : ℕ × ℕ × List ℕ}, q ∈ pairsOf L →
    L.Perm (q.1 :: q.2.1 :: q.2.2)
  | [], _, h => by simp [pairsOf] at h
  | x :: xs, q, h => by
    simp only [pairsOf, List.mem_append, List.mem_map] at h
    rcases h with ⟨⟨a, r⟩, hq, rfl⟩ | ⟨q', hq, rfl⟩
    · exact (picks_sound hq).cons x
    · exact ((pairsOf_sound hq).cons x).trans
        ((List.Perm.swap _ _ _).trans ((List.Perm.swap _ _ _).cons _))

theorem wone_bad {w : Wt} (hw : w ∈ WL) {a b : ℕ} {L : List ℕ} (h : wone w L a b = true)
    (hab : a ∈ [w.xi, w.nxi] ∧ b ∈ [w.xj, w.nxj]) : ∃ r, L.Perm (a :: b :: r) ∧ Bad a b r := by
  unfold wone at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, Bool.or_eq_true] at h
  obtain ⟨⟨hca, hcb⟩, hall⟩ := h
  have hg := wl_good w hw a hab.1 b hab.2
  unfold wgood at hg
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', bne_iff_ne, ne_eq] at hg
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hl, hm⟩, hn⟩, dP⟩, dQ⟩, ht⟩, hu⟩, hx⟩, hne⟩ := hg
  obtain ⟨⟨⟨m1, m2⟩, m3⟩, m4⟩ := hm
  obtain ⟨⟨⟨n1, n2⟩, n3⟩, n4⟩ := hn
  obtain ⟨⟨⟨t1, t2⟩, t3⟩, t4⟩ := ht
  obtain ⟨⟨⟨u1, u2⟩, u3⟩, u4⟩ := hu
  have ha : a ∈ L := List.count_pos_iff.1 (by omega)
  have hb : b ∈ L := List.count_pos_iff.1 (by omega)
  have hb' : b ∈ L.erase a := (List.mem_erase_of_ne (Ne.symm hne)).2 hb
  let r := (L.erase a).erase b
  have hp : L.Perm (a :: b :: r) := (List.perm_cons_erase ha).trans ((List.perm_cons_erase hb').cons a)
  have hra : ∀ v ∈ r, v ≠ a := by
    intro v hv e
    rw [e] at hv
    have c1 : r.count a = 0 := by
      simp only [r]
      rw [List.count_erase_of_ne hne, List.count_erase_self, hca]
    have := List.count_pos_iff.2 hv
    omega
  have hrb : ∀ v ∈ r, v ≠ b := by
    intro v hv e
    rw [e] at hv
    have c1 : r.count b = 0 := by
      simp only [r]
      rw [List.count_erase_self, List.count_erase_of_ne (Ne.symm hne), hcb]
    have := List.count_pos_iff.2 hv
    omega
  have hcm : ∀ v ∈ r, cm v w.m1 = true ∧ cm v w.m2 = true := by
    intro v hv
    have hvL : v ∈ L := List.mem_of_mem_erase (List.mem_of_mem_erase hv)
    rcases hall v hvL with (e | e) | e
    · exact absurd e (hra v hv)
    · exact absurd e (hrb v hv)
    · exact e
  refine ⟨r, hp, w.p1, w.p2, w.p3, w.p4, w.q1, w.q2, w.q3, w.q4, hl, ?_, ?_, dP, dQ,
    ⟨t1, t2, t3, t4⟩, ⟨u1, u2, u3, u4⟩, hx⟩
  · intro v hv
    have hc := (hcm v hv).1
    exact ⟨cm_eq hc m1 m2, cm_eq hc m1 m3, cm_eq hc m1 m4⟩
  · intro v hv
    have hc := (hcm v hv).2
    exact ⟨cm_eq hc n1 n2, cm_eq hc n1 n3, cm_eq hc n1 n4⟩

theorem wit_sound {L : List ℕ} (h : wit L = true) : ∃ a b r, L.Perm (a :: b :: r) ∧ Bad a b r := by
  unfold wit at h
  obtain ⟨w, hw, h⟩ := List.any_eq_true.1 h
  unfold wtry at h
  simp only [Bool.or_eq_true] at h
  rcases h with ((h | h) | h) | h
  · obtain ⟨r, hp, hb⟩ := wone_bad hw h ⟨by simp, by simp⟩; exact ⟨_, _, r, hp, hb⟩
  · obtain ⟨r, hp, hb⟩ := wone_bad hw h ⟨by simp, by simp⟩; exact ⟨_, _, r, hp, hb⟩
  · obtain ⟨r, hp, hb⟩ := wone_bad hw h ⟨by simp, by simp⟩; exact ⟨_, _, r, hp, hb⟩
  · obtain ⟨r, hp, hb⟩ := wone_bad hw h ⟨by simp, by simp⟩; exact ⟨_, _, r, hp, hb⟩

theorem Run.passOk {s : ℕ} {L : List ℕ} (h : Run TT AA s L) {s' : ℕ} (hs : s ≤ s') :
    passes s' L = true := by
  obtain ⟨hl, hc, hr⟩ := h.inv
  unfold passes
  rw [Bool.and_eq_true, Bool.and_eq_true, Nat.ble_eq, covB_of_cov hc]
  refine ⟨⟨by omega, ?_⟩, rfl⟩
  rw [Bool.not_eq_true']
  cases hw : wit L
  · simp
  · by_cases hlen : L.length = s' + 1
    · obtain ⟨a, b, r, hp, hb⟩ := wit_sound hw
      exact absurd hb (hr (by omega) a b r hp)
    · simp [hlen]

/-! ### Symmetry -/

theorem pg_bit : ∀ (p : List ℕ) (v j : ℕ), (pg p v).testBit j = (p[j]?.map v.testBit).getD false
  | [], v, j => by simp [pg]
  | q :: qs, v, 0 => by simp [pg, Nat.testBit_bit_zero]
  | q :: qs, v, j + 1 => by simp [pg, Nat.testBit_bit_succ, pg_bit qs v j]

theorem pg_and (p : List ℕ) (a b : ℕ) : pg p (a &&& b) = pg p a &&& pg p b := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_and, pg_bit, pg_bit, pg_bit]
  cases p[j]? <;> simp [Nat.testBit_and]

theorem pg_or (p : List ℕ) (a b : ℕ) : pg p (a ||| b) = pg p a ||| pg p b := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_or, pg_bit, pg_bit, pg_bit]
  cases p[j]? <;> simp [Nat.testBit_or]

theorem pg_xor (p : List ℕ) (a b : ℕ) : pg p (a ^^^ b) = pg p a ^^^ pg p b := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_xor, pg_bit, pg_bit, pg_bit]
  cases p[j]? <;> simp [Nat.testBit_xor]

def Hom (f : ℕ → ℕ) : Prop :=
  (∀ a b, f (a &&& b) = f a &&& f b) ∧ (∀ a b, f (a ||| b) = f a ||| f b) ∧
    (∀ a b, f (a ^^^ b) = f a ^^^ f b) ∧ f 0 = 0 ∧ f TT = TT ∧ f AA = AA

set_option maxHeartbeats 4000000 in
theorem sg_fix : pg SG 0 = 0 ∧ pg SG TT = TT ∧ pg SG AA = AA := by decide +kernel

theorem hom_sg : Hom (pg SG) := ⟨pg_and SG, pg_or SG, pg_xor SG, sg_fix.1, sg_fix.2.1, sg_fix.2.2⟩

theorem hom_id : Hom id := ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, rfl, rfl, rfl⟩

theorem Hom.comp {f g : ℕ → ℕ} (hf : Hom f) (hg : Hom g) : Hom (f ∘ g) := by
  obtain ⟨f1, f2, f3, f4, f5, f6⟩ := hf
  obtain ⟨g1, g2, g3, g4, g5, g6⟩ := hg
  refine ⟨fun a b => ?_, fun a b => ?_, fun a b => ?_, ?_, ?_, ?_⟩ <;>
    simp only [Function.comp_apply, f1, f2, f3, f4, f5, f6, g1, g2, g3, g4, g5, g6]

theorem hom_opv {f : ℕ → ℕ} (hf : Hom f) (o : Fin 4) (a b : ℕ) :
    f (opv AA o a b) = opv AA o (f a) (f b) := by
  fin_cases o
  · exact hf.1 a b
  · exact hf.2.1 a b
  · show f (AA ^^^ a) = AA ^^^ f a
    rw [hf.2.2.1, hf.2.2.2.2.2]
  · show f (AA ^^^ b) = AA ^^^ f b
    rw [hf.2.2.1, hf.2.2.2.2.2]

theorem hom_not {f : ℕ → ℕ} (hf : Hom f) (a : ℕ) : f (AA ^^^ a) = AA ^^^ f a := by
  rw [hf.2.2.1, hf.2.2.2.2.2]

theorem Run.mapH {f : ℕ → ℕ} (hf : Hom f) {s : ℕ} {L : List ℕ} (h : Run TT AA s L) :
    Run TT AA s (L.map f) := by
  induction h with
  | done s =>
    rw [List.map_cons, List.map_nil, hf.2.2.2.2.1]
    exact Run.done s
  | perm p _ ih => exact Run.perm (p.map _) ih
  | mono _ ih => exact Run.mono ih
  | @two s a b r o ka kb _ ih =>
    simp only [List.map_cons, map_kept, hom_opv hf] at ih ⊢
    exact Run.two o ka kb ih
  | @one s a w r ka hw _ ih =>
    simp only [List.map_cons, map_kept] at ih ⊢
    refine Run.one ka ?_ ih
    rcases hw with rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl (hom_not hf a))
    · exact Or.inr (Or.inr (Or.inl hf.2.2.2.1))
    · exact Or.inr (Or.inr (Or.inr hf.2.2.2.2.2))
  | @const s w r hw _ ih =>
    simp only [List.map_cons] at ih ⊢
    refine Run.const ?_ ih
    rcases hw with rfl | rfl
    · exact Or.inl hf.2.2.2.1
    · exact Or.inr hf.2.2.2.2.2

theorem lookS_sound {t : Tr} {s : ℕ} {L : List ℕ} (h : lookS t s L = true) :
    ∃ g, Hom g ∧ ∃ v, Mem t (srt (L.map g)) v ∧ s ≤ v := by
  unfold lookS at h
  rw [Bool.or_eq_true] at h
  rcases h with h | h
  · obtain ⟨v, hv, hs⟩ := look_sound h
    exact ⟨id, hom_id, v, by rwa [List.map_id], hs⟩
  · obtain ⟨v, hv, hs⟩ := look_sound h
    exact ⟨pg SG, hom_sg, v, hv, hs⟩

/-! ### Children -/

def Child (P c : List ℕ) : Prop :=
  (∃ a b r o ka kb, P = a :: b :: r ∧ c = opv AA o a b :: kept ka a (kept kb b r)) ∨
  (∃ a r w ka, P = a :: r ∧ (w = AA ^^^ a ∨ w = 0 ∨ w = AA ∨ (w = a ∧ ka = true)) ∧
    c = w :: kept ka a r) ∨
  (∃ w, (w = 0 ∨ w = AA) ∧ c = w :: P)

theorem child_map {f : ℕ → ℕ} (hf : Hom f) {P c : List ℕ} (h : Child P c) :
    Child (P.map f) (c.map f) := by
  rcases h with ⟨a, b, r, o, ka, kb, rfl, rfl⟩ | ⟨a, r, w, ka, rfl, hw, rfl⟩ | ⟨w, hw, rfl⟩
  · left
    refine ⟨f a, f b, r.map f, o, ka, kb, rfl, ?_⟩
    simp [map_kept, hom_opv hf]
  · right; left
    refine ⟨f a, r.map f, f w, ka, rfl, ?_, ?_⟩
    · rcases hw with rfl | rfl | rfl | ⟨rfl, rfl⟩
      · exact Or.inl (hom_not hf a)
      · exact Or.inr (Or.inl hf.2.2.2.1)
      · exact Or.inr (Or.inr (Or.inl hf.2.2.2.2.2))
      · exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))
    · simp [map_kept]
  · right; right
    refine ⟨f w, ?_, ?_⟩
    · rcases hw with rfl | rfl
      · exact Or.inl hf.2.2.2.1
      · exact Or.inr hf.2.2.2.2.2
    · simp

theorem mem_twoCh (a b : ℕ) (r : List ℕ) (o : Fin 4) (ka kb : Bool) :
    opv AA o a b :: kept ka a (kept kb b r) ∈ twoCh a b r := by
  unfold twoCh
  simp only [List.mem_flatMap, List.mem_map]
  exact ⟨o, by fin_cases o <;> simp, ka, by cases ka <;> simp, kb, by cases kb <;> simp, rfl⟩

theorem child_perm {P c K : List ℕ} (h : Child P c) (hK : K.Perm P) :
    ∃ c' ∈ children K, c'.Perm c := by
  rcases h with ⟨a, b, r, o, ka, kb, rfl, rfl⟩ | ⟨a, r, w, ka, rfl, hw, rfl⟩ | ⟨w, hw, rfl⟩
  · obtain ⟨q, hq, hab, hp⟩ := pairs_complete hK
    have hmem : ∀ o' ka' kb', opv AA o' q.1 q.2.1 :: kept ka' q.1 (kept kb' q.2.1 q.2.2) ∈ children K := by
      intro o' ka' kb'
      unfold children
      simp only [List.mem_append]
      left; left
      rw [List.mem_flatMap]
      exact ⟨q, hq, mem_twoCh _ _ _ o' ka' kb'⟩
    rcases hab with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · refine ⟨_, hmem o ka kb, ?_⟩
      rw [h1, h2]
      exact (kept_perm ka a (kept_perm kb b hp)).cons _
    · refine ⟨_, hmem (swp o) kb ka, ?_⟩
      rw [h1, h2, ← opv_swp]
      exact ((kept_perm kb b (kept_perm ka a hp)).trans (kept_swap kb ka b a r)).cons _
  · obtain ⟨r', hr', hp⟩ := pick_perm hK
    have hmem : ∀ ch ∈ [a :: a :: r', (AA ^^^ a) :: a :: r', (AA ^^^ a) :: r', 0 :: a :: r', 0 :: r',
        AA :: a :: r', AA :: r'], ch ∈ children K := by
      intro ch hch
      unfold children
      simp only [List.mem_append]
      left; right
      rw [List.mem_flatMap]
      exact ⟨(a, r'), hr', hch⟩
    rcases hw with rfl | rfl | rfl | ⟨rfl, rfl⟩
    · cases ka
      · exact ⟨_, hmem _ (by simp), hp.cons _⟩
      · exact ⟨_, hmem _ (by simp), (hp.cons a).cons _⟩
    · cases ka
      · exact ⟨_, hmem _ (by simp), hp.cons _⟩
      · exact ⟨_, hmem _ (by simp), (hp.cons a).cons _⟩
    · cases ka
      · exact ⟨_, hmem _ (by simp), hp.cons _⟩
      · exact ⟨_, hmem _ (by simp), (hp.cons a).cons _⟩
    · exact ⟨_, hmem (w :: w :: r') (by simp), (hp.cons w).cons w⟩
  · refine ⟨w :: K, ?_, hK.cons w⟩
    unfold children
    simp only [List.mem_append]
    right
    rcases hw with rfl | rfl <;> simp

/-! ### The certificate argument -/

theorem cert (t : Tr) (ht : allE t t = true) {s : ℕ} {L : List ℕ} (h : Run TT AA s L) :
    ∀ f, Hom f → ∀ v, Mem t (srt (L.map f)) v → s ≤ v → False := by
  have step : ∀ {s : ℕ} {P c : List ℕ}, Child P c → Run TT AA s c →
      (∀ f, Hom f → ∀ v, Mem t (srt (c.map f)) v → s ≤ v → False) →
      ∀ f, Hom f → ∀ v, Mem t (srt (P.map f)) v → s + 1 ≤ v → False := by
    intro s P c hch hc ih f hf v hm hv
    have hK := allE_sound t ht hm
    unfold chkE at hK
    simp only [Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hK
    obtain ⟨c', hc'm, hc'p⟩ := child_perm (child_map hf hch) (srt_perm_self (P.map f))
    have hrun : Run TT AA s c' := Run.perm hc'p.symm (hc.mapH hf)
    rcases hK.2 c' hc'm with hf' | hl
    · rw [hrun.passOk (show s ≤ v - 1 by omega)] at hf'
      cases hf'
    · obtain ⟨g, hg, w, hw, hs⟩ := lookS_sound hl
      have e : srt (c'.map g) = srt (c.map (g ∘ f)) := by
        rw [← List.map_map]
        exact srt_perm (hc'p.map _)
      rw [e] at hw
      exact ih _ (hg.comp hf) w hw (by omega)
  induction h with
  | done s =>
    intro f hf v hm _
    have e : srt ([TT].map f) = [TT] := by
      rw [List.map_cons, List.map_nil, hf.2.2.2.2.1]
      rfl
    rw [e] at hm
    have hK := allE_sound t ht hm
    unfold chkE at hK
    simp only [Bool.and_eq_true] at hK
    have : cmpL [TT] [TT] = Ordering.eq := by decide
    rw [this] at hK
    simp at hK
  | perm p _ ih =>
    intro f hf v hm hv
    rw [← srt_perm (p.map f)] at hm
    exact ih f hf v hm hv
  | mono _ ih =>
    intro f hf v hm hv
    exact ih f hf v hm (by omega)
  | @two s a b r o ka kb hc ih =>
    exact step (Or.inl ⟨a, b, r, o, ka, kb, rfl, rfl⟩) hc ih
  | @one s a w r ka hw hc ih =>
    by_cases htriv : w = a ∧ ka = false
    · obtain ⟨rfl, rfl⟩ := htriv
      intro f hf v hm hv
      exact ih f hf v hm (by omega)
    · refine step (Or.inr (Or.inl ⟨a, r, w, ka, rfl, ?_, rfl⟩)) hc ih
      rcases hw with rfl | rfl | rfl | rfl
      · cases ka
        · exact absurd ⟨rfl, rfl⟩ htriv
        · exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
  | @const s w r hw hc ih =>
    exact step (Or.inr (Or.inr ⟨w, hw, rfl⟩)) hc ih


def cv0 : ℕ := 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
def cv1 : ℕ := 0xff00ff00ff00ff00ff00ff00ff00ff00
def cv2 : ℕ := 0xffff0000ffff0000ffff0000ffff0000
def cv3 : ℕ := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0
def cv4 : ℕ := 0xffffffffffffffff0000000000000000
def cv5 : ℕ := 0xffffffff00000000ffffffff00000000
def cv6 : ℕ := 0xcccccccccccccccccccccccccccccccc
def cv7 : ℕ := 0xffffffffffffffff
def cv8 : ℕ := 0xffffffff00000000ffffffff
def cv9 : ℕ := 0x33333333333333333333333333333333
def cv10 : ℕ := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
def cv11 : ℕ := 0xffffffffcccccccccccccccccccccccc
def cv12 : ℕ := 0xffffccccccccccccffffcccccccccccc
def cv13 : ℕ := 0xffffffffaaaaaaaaffffffffaaaaaaaa
def cv14 : ℕ := 0xffccccccffccccccffccccccffcccccc
def cv15 : ℕ := 0xffffffffffffffffaaaaaaaaaaaaaaaa
def cv16 : ℕ := 0xffccffccffccffccffccffccffccffcc
def cv17 : ℕ := 0xffff0000ff000000ffff0000ff000000
def cv18 : ℕ := 0xffffffffccccccccffffcccccccccccc
def cv19 : ℕ := 0xffffffffffffffffffff000000000000
def cv20 : ℕ := 0xfffff0f0f0f0f0f0fffff0f0f0f0f0f0
def cv21 : ℕ := 0xffffccccffccccccffffccccffcccccc
def cv22 : ℕ := 0xff000000ff000000ff000000ff000000
def cv23 : ℕ := 0xffffaaaaffffaaaaffffaaaaffffaaaa
def cv24 : ℕ := 0xffffffffccccccccffffffffcccccccc
def cv25 : ℕ := 0xffffccccffffccccffffccccffffcccc
def cv26 : ℕ := 0xffff000000000000ffff000000000000
def cv27 : ℕ := 0xffffffffff00ff00ffffffffff00ff00
def cv28 : ℕ := 0xfff0fff0fff0fff0fff0fff0fff0fff0
def cv29 : ℕ := 0xeecceecceecceecceecceecceecceecc
def cv30 : ℕ := 0xffffaaaaaaaaaaaaffffaaaaaaaaaaaa
def cv31 : ℕ := 0xfffffffffffffffff0f0f0f0f0f0f0f0
def cv32 : ℕ := 0xfffff0f0fff0f0f0fffff0f0fff0f0f0
def cv33 : ℕ := 0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee
def cv34 : ℕ := 0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0
def cv35 : ℕ := 0xffffffffffffffffffff0000ffff0000
def cv36 : ℕ := 0xffffffffff000000ffffffffff000000
def cv37 : ℕ := 0xaa00aa00aa00aa00aa00aa00aa00aa00
def cv38 : ℕ := 0xfaf0faf0faf0faf0faf0faf0faf0faf0
def cv39 : ℕ := 0xffaaaaaaffaaaaaaffaaaaaaffaaaaaa
def cv40 : ℕ := 0xff00aa00ff00aa00ff00aa00ff00aa00
def cv41 : ℕ := 0xfafafafafafafafafafafafafafafafa
def cv42 : ℕ := 0xffffffff00000000ffff000000000000
def cv43 : ℕ := 0xeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaea
def cv44 : ℕ := 0xffffffffaaaaaaaaffffaaaaaaaaaaaa
def cv45 : ℕ := 0xffffffffffffffffff00ff00ff00ff00
def cv46 : ℕ := 0xfff0f0f0fff0f0f0fff0f0f0fff0f0f0
def cv47 : ℕ := 0xecececececececececececececececec
def cv48 : ℕ := 0xa8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8
def cv49 : ℕ := 0x55555555555555555555555555555555
def cv50 : ℕ := 0xfffff0f0fffff0f0fffff0f0fffff0f0
def cv51 : ℕ := 0xffffffffffff0000ffff0000ffff0000
def cv52 : ℕ := 0xffffaaaaffaaaaaaffffaaaaffaaaaaa
def cv53 : ℕ := 0xffffffffffffffffff000000ff000000
def cv54 : ℕ := 0xf0f00000f0f00000f0f00000f0f00000
def cv55 : ℕ := 0xffffaa00ffffaa00ffffaa00ffffaa00
def cv56 : ℕ := 0xffffff00ff00ff00ffffff00ff00ff00
def cv57 : ℕ := 0xffffffffffffffffc0c0c0c0c0c0c0c0
def cv58 : ℕ := 0xffaaffaaffaaffaaffaaffaaffaaffaa
def cv59 : ℕ := 0xffffffff88888888ffffffff88888888
def t0 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [0x0, cv7, cv0, cv6, cv3, cv1, cv2, cv5] 8 Tr.E) [0x0, cv8, cv0, cv6, cv3, cv1, cv2, cv4] 8 (Tr.N Tr.E [0x0, cv10, cv0, cv6, cv1, cv2, cv5, cv4] 8 Tr.E)) [0x0, cv9, cv0, cv3, cv1, cv2, cv5, cv4] 8 (Tr.N (Tr.N Tr.E [0x0, cv0, cv6, cv3, cv1, cv2, cv5, cv4] 9 Tr.E) [0xffffffff, cv0, cv6, cv3, cv1, cv2, cv5, cv4] 8 Tr.E)) [0xffff0000ffff, cv0, cv6, cv3, cv1, cv2, cv5, cv4] 8 (Tr.N (Tr.N (Tr.N Tr.E [0xffffffffffff, cv0, cv6, cv3, cv1, cv2, cv5] 7 Tr.E) [0xff00ff00ff00ff, cv0, cv6, cv3, cv1, cv2, cv5, cv4] 8 (Tr.N Tr.E [0xffffff00ffffff, cv0, cv6, cv3, cv1, cv2, cv5] 7 Tr.E)) [0xf0f0f0f0f0f0f0f, cv0, cv6, cv3, cv1, cv2, cv5, cv4] 8 (Tr.N (Tr.N Tr.E [0xf0fffff0f0fffff, cv0, cv6, cv3, cv1, cv2, cv5] 7 Tr.E) [0x3333333333333333, cv0, cv6, cv3, cv1, cv2, cv5, cv4] 8 Tr.E))) [0x3f3f3f3f3f3f3f3f, cv0, cv6, cv3, cv1, cv2, cv5] 7 (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [0x5555555555555555, cv0, cv6, cv3, cv1, cv2, cv5, cv4] 8 Tr.E) [0x5555ffff5555ffff, cv0, cv6, cv3, cv1, cv2, cv5] 7 (Tr.N Tr.E [0x55ff55ff55ff55ff, cv0, cv6, cv3, cv1, cv2, cv5] 7 Tr.E)) [0x5f5f5f5f5f5f5f5f, cv0, cv6, cv3, cv1, cv2, cv5] 7 (Tr.N (Tr.N Tr.E [0x7777777777777777, cv0, cv6, cv3, cv1, cv2, cv5] 7 Tr.E) [0xaaaaaaaaaaaaaaaa, cv7, cv0, cv6, cv3, cv1, cv2, cv5] 8 Tr.E)) [0xaaaaaaaaaaaaaaaa, cv0, cv6, cv3, cv1, cv2, cv5, cv4] 8 (Tr.N (Tr.N (Tr.N Tr.E [0xcccccccccccccccc, cv7, cv0, cv6, cv3, cv1, cv2, cv5] 8 Tr.E) [0xcccccccccccccccc, cv0, cv6, cv3, cv1, cv2, cv5, cv4] 8 Tr.E) [0xf0f0f0f0f0f0f0f0, cv7, cv0, cv6, cv3, cv1, cv2, cv5] 8 (Tr.N (Tr.N Tr.E [0xf0f0f0f0f0f0f0f0, cv0, cv6, cv3, cv1, cv2, cv5, cv4] 8 Tr.E) [0xff00ff00ff00ff00, cv7, cv0, cv6, cv3, cv1, cv2, cv5] 8 Tr.E))))
def t1 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [0xffff0000ffff0000, cv7, cv0, cv6, cv3, cv1, cv2, cv5] 8 Tr.E) [0xffff0000ffff0000, cv0, cv6, cv3, cv1, cv2, cv5, cv4] 8 (Tr.N Tr.E [0xffffffff00000000, cv7, cv0, cv6, cv3, cv1, cv2, cv5] 8 Tr.E)) [0xffffffff00000000, cv0, cv6, cv3, cv1, cv2, cv5, cv4] 8 (Tr.N (Tr.N Tr.E [0xffffffffcccccccc, cv0, cv6, cv3, cv1, cv2, cv5] 7 Tr.E) [0xffffffffffff0000, cv0, cv6, cv3, cv1, cv2, cv5] 7 Tr.E)) [cv7, cv7, cv0, cv6, cv3, cv1, cv2, cv5] 8 (Tr.N (Tr.N (Tr.N Tr.E [cv7, cv8, 0xffff0000ffff0000ffff0000ffff, cv0, cv6, cv3, cv1] 7 Tr.E) [cv7, cv8, 0xff00ff00ff00ff00ff00ff00ff00ff, cv0, cv6, cv3, cv2] 7 (Tr.N Tr.E [cv7, cv8, cv10, cv0, cv6, cv1, cv2] 7 Tr.E)) [cv7, cv8, cv9, cv0, cv3, cv1, cv2] 7 (Tr.N (Tr.N Tr.E [cv7, cv8, cv49, cv6, cv3, cv1, cv2] 7 Tr.E) [cv7, cv8, cv0, cv6, cv3, cv1, cv2] 8 Tr.E))) [cv7, cv8, cv0, cv6, cv3, cv1, cv2, cv5] 8 (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv7, cv8, cv0, cv6, cv3, cv1, cv2, cv4] 8 Tr.E) [cv7, 0xffff0000ffff0000ffff0000ffff, cv10, cv0, cv6, cv1, cv5] 7 (Tr.N Tr.E [cv7, 0xffff0000ffff0000ffff0000ffff, cv9, cv0, cv3, cv1, cv5] 7 Tr.E)) [cv7, 0xffff0000ffff0000ffff0000ffff, cv49, cv6, cv3, cv1, cv5] 7 (Tr.N (Tr.N Tr.E [cv7, 0xffff0000ffff0000ffff0000ffff, cv0, cv6, cv3, cv1, cv2, cv5] 8 Tr.E) [cv7, 0xffff0000ffff0000ffff0000ffff, cv0, cv6, cv3, cv1, cv5] 8 Tr.E)) [cv7, 0xffff0000ffff0000ffff0000ffff, cv0, cv6, cv3, cv1, cv5, cv4] 8 (Tr.N (Tr.N (Tr.N Tr.E [cv7, 0xff00ff00ff00ff00ff00ff00ff00ff, cv10, cv0, cv6, cv2, cv5] 7 Tr.E) [cv7, 0xff00ff00ff00ff00ff00ff00ff00ff, cv9, cv0, cv3, cv2, cv5] 7 Tr.E) [cv7, 0xff00ff00ff00ff00ff00ff00ff00ff, cv0, cv6, cv3, cv1, cv2, cv5] 8 (Tr.N (Tr.N Tr.E [cv7, 0xff00ff00ff00ff00ff00ff00ff00ff, cv0, cv6, cv3, cv2, cv5] 8 Tr.E) [cv7, cv10, cv9, cv0, cv1, cv2, cv5] 7 Tr.E))))
def u2 : Tr := Tr.N t0 [0xff00ff00ff00ff00, cv0, cv6, cv3, cv1, cv2, cv5, cv4] 8 t1
def t3 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv7, cv10, cv0, cv6, cv3, cv1, cv2, cv5] 8 Tr.E) [cv7, cv10, cv0, cv6, cv1, cv2, cv5] 8 (Tr.N Tr.E [cv7, cv10, cv0, cv6, cv1, cv2, cv5, cv4] 8 Tr.E)) [cv7, cv9, cv49, cv3, cv1, cv2, cv5] 7 (Tr.N (Tr.N Tr.E [cv7, cv9, cv0, cv6, cv3, cv1, cv2, cv5] 8 Tr.E) [cv7, cv9, cv0, cv3, cv1, cv2, cv5] 8 Tr.E)) [cv7, cv9, cv0, cv3, cv1, cv2, cv5, cv4] 8 (Tr.N (Tr.N (Tr.N Tr.E [cv7, cv49, cv0, cv6, cv3, cv1, cv2, cv5] 8 Tr.E) [cv7, cv49, cv6, cv3, cv1, cv2, cv5] 8 (Tr.N Tr.E [cv7, cv49, cv6, cv3, cv1, cv2, cv5, cv4] 8 Tr.E)) [cv7, 0x88888888888888888888888888888888, cv0, cv6, cv3, cv1, cv2, cv5] 8 (Tr.N (Tr.N Tr.E [cv7, cv34, cv0, cv6, cv3, cv1, cv2, cv5] 8 Tr.E) [cv7, 0xa0a0a0a0a0a0a0a0aaaaaaaaaaaaaaaa, cv6, cv3, cv1, cv2, cv5] 7 Tr.E))) [cv7, 0xa0a0a0a0a0a0a0a0f0f0f0f0f0f0f0f0, cv0, cv6, cv1, cv2, cv5] 7 (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv7, cv48, cv6, cv3, cv1, cv2, cv5] 7 Tr.E) [cv7, cv37, cv0, cv6, cv3, cv1, cv2, cv5] 8 (Tr.N Tr.E [cv7, 0xaaaa0000aaaa0000aaaa0000aaaa0000, cv0, cv6, cv3, cv1, cv2, cv5] 8 Tr.E)) [cv7, 0xaaaaaa00aaaaaa00aaaaaa00aaaaaa00, cv6, cv3, cv1, cv2, cv5] 7 (Tr.N (Tr.N Tr.E [cv7, 0xaaaaaaaa00000000aaaaaaaa00000000, cv0, cv6, cv3, cv1, cv2, cv5] 8 Tr.E) [cv7, 0xaaaaaaaaaaaaaaaa0000000000000000, cv0, cv6, cv3, cv1, cv2, cv5] 8 Tr.E)) [cv7, cv0, cv0, cv6, cv3, cv1, cv2, cv5] 8 (Tr.N (Tr.N (Tr.N Tr.E [cv7, cv0, 0xaaaaaaaaaaaaaaaaffffffffffffffff, cv6, cv3, cv1, cv2, cv5] 8 Tr.E) [cv7, cv0, 0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0, cv6, cv3, cv1, cv2, cv5] 8 Tr.E) [cv7, cv0, 0xc8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8, cv3, cv1, cv2, cv5] 7 (Tr.N (Tr.N Tr.E [cv7, cv0, 0xcc00cc00cc00cc00cc00cc00cc00cc00, cv6, cv3, cv1, cv2, cv5] 8 Tr.E) [cv7, cv0, 0xcccc0000cccc0000cccc0000cccc0000, cv6, cv3, cv1, cv2, cv5] 8 Tr.E))))
def t4 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv7, cv0, 0xcccccccccccccccc0000000000000000, cv6, cv3, cv1, cv2, cv5] 8 Tr.E) [cv7, cv0, 0xcccccccccccccccccccccccc00000000, cv3, cv1, cv2, cv5] 7 (Tr.N Tr.E [cv7, cv0, cv6, cv6, cv3, cv1, cv2, cv5] 8 Tr.E)) [cv7, cv0, cv6, 0xccccccccccccccccffffffffffffffff, cv3, cv1, cv2, cv5] 8 (Tr.N (Tr.N Tr.E [cv7, cv0, cv6, 0xe0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0, cv1, cv2, cv5] 7 Tr.E) [cv7, cv0, cv6, cv33, cv3, cv1, cv2, cv5] 8 Tr.E)) [cv7, cv0, cv6, 0xf000f000f000f000f000f000f000f000, cv3, cv1, cv2, cv5] 8 (Tr.N (Tr.N (Tr.N Tr.E [cv7, cv0, cv6, cv54, cv3, cv1, cv2, cv5] 8 Tr.E) [cv7, cv0, cv6, 0xf0f00000f0f00000f0f0f0f0f0f0f0f0, cv1, cv2, cv5] 7 Tr.E) [cv7, cv0, cv6, 0xf0f00000f0f00000ffff0000ffff0000, cv3, cv1, cv5] 7 (Tr.N (Tr.N Tr.E [cv7, cv0, cv6, 0xf0f0f0f000000000f0f0f0f000000000, cv3, cv1, cv2, cv5] 8 Tr.E) [cv7, cv0, cv6, 0xf0f0f0f0f0f00000f0f0f0f0f0f00000, cv1, cv2, cv5] 7 Tr.E))) [cv7, cv0, cv6, 0xf0f0f0f0f0f0f0f00000000000000000, cv3, cv1, cv2, cv5] 8 (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv7, cv0, cv6, cv3, cv3, cv1, cv2, cv5] 8 Tr.E) [cv7, cv0, cv6, cv3, 0xf0f0f0f0f0f0f0f0ffffffffffffffff, cv1, cv2, cv5] 8 (Tr.N Tr.E [cv7, cv0, cv6, cv3, cv41, cv1, cv2, cv5] 8 Tr.E)) [cv7, cv0, cv6, cv3, 0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc, cv1, cv2, cv5] 8 (Tr.N (Tr.N Tr.E [cv7, cv0, cv6, cv3, cv22, cv1, cv2, cv5] 8 Tr.E) [cv7, cv0, cv6, cv3, 0xff000000ff000000ff00ff00ff00ff00, cv2, cv5] 7 Tr.E)) [cv7, cv0, cv6, cv3, 0xff000000ff000000ffff0000ffff0000, cv1, cv5] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv7, cv0, cv6, cv3, cv40, cv2, cv5] 7 Tr.E) [cv7, cv0, cv6, cv3, 0xff00ff0000000000ff00ff0000000000, cv1, cv2, cv5] 8 Tr.E) [cv7, cv0, cv6, cv3, 0xff00ff00ff000000ff00ff00ff000000, cv2, cv5] 7 (Tr.N (Tr.N Tr.E [cv7, cv0, cv6, cv3, 0xff00ff00ff00ff000000000000000000, cv1, cv2, cv5] 8 Tr.E) [cv7, cv0, cv6, cv3, cv1, cv1, cv2, cv5] 8 Tr.E))))
def u5 : Tr := Tr.N t3 [cv7, cv0, 0xcccccccc00000000cccccccc00000000, cv6, cv3, cv1, cv2, cv5] 8 t4
def u6 : Tr := Tr.N u2 [cv7, cv10, cv49, cv6, cv1, cv2, cv5] 7 u5
def t7 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv7, cv0, cv6, cv3, cv1, 0xffaa0000ffaa0000ffaa0000ffaa0000, cv5] 7 Tr.E) [cv7, cv0, cv6, cv3, cv1, cv58, cv2, cv5] 8 (Tr.N Tr.E [cv7, cv0, cv6, cv3, cv1, cv16, cv2, cv5] 8 Tr.E)) [cv7, cv0, cv6, cv3, cv1, cv28, cv2, cv5] 8 (Tr.N (Tr.N Tr.E [cv7, cv0, cv6, cv3, cv1, cv26, cv2, cv5] 8 Tr.E) [cv7, cv0, cv6, cv3, cv1, 0xffff0000f0f00000ffff0000f0f00000, cv5] 7 Tr.E)) [cv7, cv0, cv6, cv3, cv1, cv17, cv5] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv7, cv0, cv6, cv3, cv1, 0xffff0000ffff00000000000000000000, cv2, cv5] 8 Tr.E) [cv7, cv0, cv6, cv3, cv1, 0xffff0000ffff0000ffff000000000000, cv5] 7 (Tr.N Tr.E [cv7, cv0, cv6, cv3, cv1, cv2, cv2, cv5] 8 Tr.E)) [cv7, cv0, cv6, cv3, cv1, cv2, 0xffff0000ffff0000ffffffffffffffff, cv5] 8 (Tr.N (Tr.N Tr.E [cv7, cv0, cv6, cv3, cv1, cv2, cv23, cv5] 8 Tr.E) [cv7, cv0, cv6, cv3, cv1, cv2, cv25, cv5] 8 Tr.E))) [cv7, cv0, cv6, cv3, cv1, cv2, 0xfffff0f000000000fffff0f000000000] 7 (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv7, cv0, cv6, cv3, cv1, cv2, cv50, cv5] 8 Tr.E) [cv7, cv0, cv6, cv3, cv1, cv2, 0xffffff0000000000ffffff0000000000] 7 (Tr.N Tr.E [cv7, cv0, cv6, cv3, cv1, cv2, 0xffffff00ffffff00ffffff00ffffff00, cv5] 8 Tr.E)) [cv7, cv0, cv6, cv3, cv1, cv2, 0xffffffff000000000000000000000000, cv5] 8 (Tr.N (Tr.N Tr.E [cv7, cv0, cv6, cv3, cv1, cv2, 0xffffffff00000000cccccccc00000000] 7 Tr.E) [cv7, cv0, cv6, cv3, cv1, cv2, cv42] 7 Tr.E)) [cv7, cv0, cv6, cv3, cv1, cv2, cv5] 9 (Tr.N (Tr.N (Tr.N Tr.E [cv7, cv0, cv6, cv3, cv1, cv2, cv5, cv5] 8 Tr.E) [cv7, cv0, cv6, cv3, cv1, cv2, cv5, 0xffffffff00000000ffffffffffffffff] 8 Tr.E) [cv7, cv0, cv6, cv3, cv1, cv2, cv5, cv13] 8 (Tr.N (Tr.N Tr.E [cv7, cv0, cv6, cv3, cv1, cv2, cv5, cv24] 8 Tr.E) [cv7, cv0, cv6, cv3, cv1, cv2, cv5, 0xfffffffff0f0f0f0fffffffff0f0f0f0] 8 Tr.E))))
def t8 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv7, cv0, cv6, cv3, cv1, cv2, cv5, 0xffffffffffff0000ffffffffffff0000] 8 Tr.E) [cv7, cv0, cv6, cv3, cv1, cv2, cv5, cv4] 9 (Tr.N Tr.E [cv7, cv0, cv6, cv3, cv1, cv2, cv5, cv15] 8 Tr.E)) [cv7, cv0, cv6, cv3, cv1, cv2, cv5, 0xffffffffffffffffcccccccccccccccc] 8 (Tr.N (Tr.N Tr.E [cv7, cv0, cv6, cv3, cv1, cv2, cv5, cv31] 8 Tr.E) [cv7, cv0, cv6, cv3, cv1, cv2, cv5, cv45] 8 Tr.E)) [cv7, cv0, cv6, cv3, cv1, cv2, cv5, cv35] 8 (Tr.N (Tr.N (Tr.N Tr.E [cv7, cv0, cv6, cv3, cv1, cv2, cv5, 0xffffffffffffffffffffffff00000000] 8 Tr.E) [cv7, cv0, cv6, cv3, cv1, cv2, cv5, 0xffffffffffffffffffffffffffffffff] 8 (Tr.N Tr.E [cv7, cv0, cv6, cv3, cv1, cv2, 0xffffffff00000000ffffffffaaaaaaaa] 7 Tr.E)) [cv7, cv0, cv6, cv3, cv1, cv2, 0xffffffff00000000fffffffff0f0f0f0] 7 (Tr.N (Tr.N Tr.E [cv7, cv0, cv6, cv3, cv1, cv2, 0xffffffff00000000ffffffffff00ff00] 7 Tr.E) [cv7, cv0, cv6, cv3, cv1, cv2, cv59] 7 Tr.E))) [cv7, cv0, cv6, cv3, cv1, cv2, 0xffffffffa0a0a0a0ffffffffa0a0a0a0] 7 (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv7, cv0, cv6, cv3, cv1, cv2, 0xffffffffaa00aa00ffffffffaa00aa00] 7 Tr.E) [cv7, cv0, cv6, cv3, cv1, cv2, 0xffffffffc0c0c0c0ffffffffc0c0c0c0] 7 (Tr.N Tr.E [cv7, cv0, cv6, cv3, cv1, cv2, 0xffffffffcc00cc00ffffffffcc00cc00] 7 Tr.E)) [cv7, cv0, cv6, cv3, cv1, cv2, 0xffffffffccccccccffffffff00000000] 7 (Tr.N (Tr.N Tr.E [cv7, cv0, cv6, cv3, cv1, cv2, cv36] 7 Tr.E) [cv7, cv0, cv6, cv3, cv1, 0xffff8888ffff8888ffff8888ffff8888, cv5] 7 Tr.E)) [cv7, cv0, cv6, cv3, cv1, 0xffffa0a0ffffa0a0ffffa0a0ffffa0a0, cv5] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv7, cv0, cv6, cv3, cv1, cv55, cv5] 7 Tr.E) [cv7, cv0, cv6, cv3, cv1, 0xffffaaaaffffaaaaffff0000ffff0000, cv5] 7 Tr.E) [cv7, cv0, cv6, cv3, cv1, 0xffffc0c0ffffc0c0ffffc0c0ffffc0c0, cv5] 7 (Tr.N (Tr.N Tr.E [cv7, cv0, cv6, cv3, cv1, 0xffffccccffffccccffff0000ffff0000, cv5] 7 Tr.E) [cv7, cv0, cv6, cv3, cv1, cv5, cv51] 7 Tr.E))))
def u9 : Tr := Tr.N t7 [cv7, cv0, cv6, cv3, cv1, cv2, cv5, cv27] 8 t8
def t10 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv7, cv0, cv6, cv3, 0xff88ff88ff88ff88ff88ff88ff88ff88, cv2, cv5] 7 Tr.E) [cv7, cv0, cv6, cv3, 0xffa0ffa0ffa0ffa0ffa0ffa0ffa0ffa0, cv2, cv5] 7 (Tr.N Tr.E [cv7, cv0, cv6, cv3, 0xffc0ffc0ffc0ffc0ffc0ffc0ffc0ffc0, cv2, cv5] 7 Tr.E)) [cv7, cv0, cv6, cv3, 0xffccffccff00ff00ffccffccff00ff00, cv2, cv5] 7 (Tr.N (Tr.N Tr.E [cv7, cv0, cv6, cv3, 0xffccffccffccffccff00ff00ff00ff00, cv2, cv5] 7 Tr.E) [cv7, cv0, cv6, cv3, 0xfff0fff0ff00ff00fff0fff0ff00ff00, cv2, cv5] 7 Tr.E)) [cv7, cv0, cv6, cv3, cv2, cv56, cv5] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv7, cv0, cv6, cv3, cv2, cv5, 0xffffffffff00ff00ff00ff00ff00ff00] 7 Tr.E) [cv7, cv0, cv6, 0xf8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8, cv1, cv2, cv5] 7 (Tr.N Tr.E [cv7, cv0, cv6, cv38, cv1, cv2, cv5] 7 Tr.E)) [cv7, cv0, cv6, 0xfcfcfcfcfcfcfcfcf0f0f0f0f0f0f0f0, cv1, cv2, cv5] 7 (Tr.N (Tr.N Tr.E [cv7, cv0, cv6, cv1, cv46, cv2, cv5] 7 Tr.E) [cv7, cv0, cv6, cv1, 0xfff0fff0fff0fff0f0f0f0f0f0f0f0f0, cv2, cv5] 7 Tr.E))) [cv7, cv0, cv6, cv1, cv2, cv20, cv5] 7 (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv7, cv0, cv6, cv1, cv2, cv5, 0xfffffffff0f0f0f0f0f0f0f0f0f0f0f0] 7 Tr.E) [cv7, cv0, 0xccccccccccccccccffffccccffffcccc, cv3, cv1, cv2, cv5] 7 (Tr.N Tr.E [cv7, cv0, cv47, cv3, cv1, cv2, cv5] 7 Tr.E)) [cv7, cv0, cv29, cv3, cv1, cv2, cv5] 7 (Tr.N (Tr.N Tr.E [cv7, cv0, cv3, cv1, cv14, cv2, cv5] 7 Tr.E) [cv7, cv0, cv3, cv1, cv2, cv12, cv5] 7 Tr.E)) [cv7, cv0, cv3, cv1, cv2, cv12, cv13] 6 (Tr.N (Tr.N (Tr.N Tr.E [cv7, cv0, cv3, cv1, cv2, cv5, cv11] 7 Tr.E) [cv7, cv0, cv1, cv21, cv32, cv5] 5 Tr.E) [cv7, cv6, cv43, cv3, cv1, cv2, cv5] 7 (Tr.N (Tr.N Tr.E [cv7, cv6, 0xeeeeeeeeeeeeeeeeaaaaaaaaaaaaaaaa, cv3, cv1, cv2, cv5] 7 Tr.E) [cv7, cv6, cv3, cv1, cv39, cv2, cv5] 7 Tr.E))))
def t11 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv7, cv6, cv3, cv1, cv2, cv5, 0xffffffffaaaaaaaaaaaaaaaaaaaaaaaa] 7 Tr.E) [cv7, cv6, cv3, cv1, cv30, cv25, cv5] 6 (Tr.N Tr.E [cv7, cv6, cv1, cv2, cv44, 0xfffffffff0f0f0f0fffff0f0f0f0f0f0] 5 Tr.E)) [cv7, cv3, cv1, cv2, cv30, cv12, cv5] 6 (Tr.N (Tr.N Tr.E [cv7, cv3, cv1, cv2, cv44, cv18] 5 Tr.E) [cv7, cv3, cv1, cv52, cv21, cv5] 5 Tr.E)) [0xffff000000000000ffff, cv0, cv6, cv3, cv1, cv2, cv5, cv4] 8 (Tr.N (Tr.N (Tr.N Tr.E [0xffff0000ffff0000ffff, cv0, cv6, cv3, cv1, cv5, cv4] 7 Tr.E) [0xffffffffffffffffffff, cv0, cv6, cv3, cv1, cv2, cv5] 7 Tr.E) [0xf0f0f0f000000000f0f0f0f, cv0, cv6, cv3, cv1, cv2, cv5, cv4] 8 (Tr.N (Tr.N Tr.E [0xf0f0f0f00000f0f0f0f0f0f, cv6, cv1, cv2, cv44, cv4] 5 Tr.E) [0xf0f0f0f0f0f0f0f0f0f0f0f, cv0, cv6, cv1, cv2, cv5, cv4] 7 Tr.E))) [0x333333330000000033333333, cv0, cv6, cv3, cv1, cv2, cv5, cv4] 8 (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [0x3333333300000000ffffffff, cv0, cv6, cv3, cv1, cv2, cv4] 7 Tr.E) [0x333333330000333333333333, cv3, cv1, cv2, cv44, cv4] 5 (Tr.N Tr.E [0x333333333333333333333333, cv0, cv3, cv1, cv2, cv5, cv4] 7 Tr.E)) [0x33333333ffffffffffffffff, cv0, cv6, cv3, cv1, cv2, cv5] 7 (Tr.N (Tr.N Tr.E [0x33ff33ff0000000033ff33ff, cv0, cv6, cv3, cv1, cv2, cv4] 7 Tr.E) [0x3f3f3f3f000000003f3f3f3f, cv0, cv6, cv3, cv1, cv2, cv4] 7 Tr.E)) [0x555555550000000055555555, cv0, cv6, cv3, cv1, cv2, cv5, cv4] 8 (Tr.N (Tr.N (Tr.N Tr.E [0x555555550000000055555555, cv0, cv3, cv1, cv2, cv12, cv4] 6 Tr.E) [0x555555550000555555555555, cv6, cv1, cv2, 0xfffffffff0f0f0f0fffff0f0f0f0f0f0, cv4] 5 Tr.E) [0x555555550000555555555555, cv3, cv1, cv2, cv18, cv4] 5 (Tr.N (Tr.N Tr.E [0x555555555555555555555555, cv6, cv3, cv1, cv2, cv5, cv4] 7 Tr.E) [0x55ff55ff0000000055ff55ff, cv0, cv6, cv3, cv1, cv2, cv4] 7 Tr.E))))
def u12 : Tr := Tr.N t10 [cv7, cv6, cv3, cv1, cv2, cv30, cv5] 7 t11
def u13 : Tr := Tr.N u9 [cv7, cv0, cv6, cv3, 0xff00ff00ff00ff00fff0fff0fff0fff0, cv2, cv5] 7 u12
def u14 : Tr := Tr.N u6 [cv7, cv0, cv6, cv3, cv1, 0xff00ff00ff00ff00ffffffffffffffff, cv2, cv5] 8 u13
def t15 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [0x777777770000000077777777, cv0, cv6, cv3, cv1, cv2, cv4] 7 Tr.E) [0xaaaaaaaa00000000aaaaaaaa, cv8, cv0, cv6, cv3, cv1, cv2, cv4] 8 (Tr.N Tr.E [0xaaaaaaaa00000000aaaaaaaa, cv0, cv6, cv3, cv1, cv2, cv5, cv4] 8 Tr.E)) [0xaaaaaaaaaaaaaaaaaaaaaaaa, cv6, cv3, cv1, cv2, cv5, cv4] 7 (Tr.N (Tr.N Tr.E [0xcccccccc00000000cccccccc, cv8, cv0, cv6, cv3, cv1, cv2, cv4] 8 Tr.E) [0xcccccccc00000000cccccccc, cv0, cv6, cv3, cv1, cv2, cv5, cv4] 8 Tr.E)) [0xcccccccccccccccccccccccc, cv0, cv3, cv1, cv2, cv5, cv4] 7 (Tr.N (Tr.N (Tr.N Tr.E [0xf0f0f0f000000000f0f0f0f0, cv8, cv0, cv6, cv3, cv1, cv2, cv4] 8 Tr.E) [0xf0f0f0f000000000f0f0f0f0, cv0, cv6, cv3, cv1, cv2, cv5, cv4] 8 (Tr.N Tr.E [0xf0f0f0f0f0f0f0f0f0f0f0f0, cv0, cv6, cv1, cv2, cv5, cv4] 7 Tr.E)) [0xff00ff0000000000ff00ff00, cv8, cv0, cv6, cv3, cv1, cv2, cv4] 8 (Tr.N (Tr.N Tr.E [0xff00ff0000000000ff00ff00, cv0, cv6, cv3, cv1, cv2, cv5, cv4] 8 Tr.E) [0xff00ff00ff00ff00ff00ff00, cv0, cv6, cv3, cv2, cv5, cv4] 7 Tr.E))) [0xffff000000000000ffff0000, cv8, cv0, cv6, cv3, cv1, cv2, cv4] 8 (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [0xffff000000000000ffff0000, cv0, cv6, cv3, cv1, cv2, cv5, cv4] 8 Tr.E) [0xffff0000ffff0000ffff0000, cv0, cv6, cv3, cv1, cv5, cv4] 7 (Tr.N Tr.E [0xfffff0f000000000fffff0f0, cv0, cv6, cv3, cv1, cv2, cv4] 7 Tr.E)) [0xffffff0000000000ffffff00, cv0, cv6, cv3, cv1, cv2, cv4] 7 (Tr.N (Tr.N Tr.E [0xffffffff0000000000000000, cv8, cv0, cv6, cv3, cv1, cv2, cv4] 8 Tr.E) [0xffffffff0000000000000000, cv0, cv6, cv3, cv1, cv2, cv5, cv4] 8 Tr.E)) [0xffffffff00000000cccccccc, cv0, cv6, cv3, cv1, cv2, cv4] 7 (Tr.N (Tr.N (Tr.N Tr.E [0xffffffff00000000ffff0000, cv0, cv6, cv3, cv1, cv2, cv4] 7 Tr.E) [cv8, cv8, cv0, cv6, cv3, cv1, cv2, cv4] 8 Tr.E) [cv8, 0xffff0000ffff0000ffff0000ffff, cv10, cv0, cv6, cv1, cv4] 7 (Tr.N (Tr.N Tr.E [cv8, 0xffff0000ffff0000ffff0000ffff, cv9, cv0, cv3, cv1, cv4] 7 Tr.E) [cv8, 0xffff0000ffff0000ffff0000ffff, cv0, cv6, cv3, cv1, cv2, cv4] 8 Tr.E))))
def t16 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv8, cv10, cv9, cv0, cv1, cv2, cv4] 7 Tr.E) [cv8, cv10, cv49, cv6, cv1, cv2, cv4] 7 (Tr.N Tr.E [cv8, cv10, cv0, cv6, cv3, cv1, cv2, cv4] 8 Tr.E)) [cv8, cv10, cv0, cv6, cv1, cv2, cv5, cv4] 8 (Tr.N (Tr.N Tr.E [cv8, cv10, cv0, cv6, cv1, cv2, cv4] 8 Tr.E) [cv8, cv9, cv49, cv3, cv1, cv2, cv4] 7 Tr.E)) [cv8, cv9, cv0, cv6, cv3, cv1, cv2, cv4] 8 (Tr.N (Tr.N (Tr.N Tr.E [cv8, cv9, cv0, cv3, cv1, cv2, cv5, cv4] 8 Tr.E) [cv8, cv9, cv0, cv3, cv1, cv2, cv4] 8 (Tr.N Tr.E [cv8, cv49, cv0, cv6, cv3, cv1, cv2, cv4] 8 Tr.E)) [cv8, cv49, cv6, cv3, cv1, cv2, cv5, cv4] 8 (Tr.N (Tr.N Tr.E [cv8, cv49, cv6, cv3, cv1, cv2, cv4] 8 Tr.E) [cv8, 0x88888888888888888888888888888888, cv0, cv6, cv3, cv1, cv2, cv4] 8 Tr.E))) [cv8, cv34, cv0, cv6, cv3, cv1, cv2, cv4] 8 (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv8, cv48, cv6, cv3, cv1, cv2, cv4] 7 Tr.E) [cv8, cv37, cv0, cv6, cv3, cv1, cv2, cv4] 8 (Tr.N Tr.E [cv8, 0xaa00aa00aaaaaaaaaa00aa00aaaaaaaa, cv6, cv3, cv1, cv2, cv4] 7 Tr.E)) [cv8, 0xaa00aa00ff00ff00aa00aa00ff00ff00, cv0, cv6, cv3, cv2, cv4] 7 (Tr.N (Tr.N Tr.E [cv8, 0xaaaa0000aaaa0000aaaa0000aaaa0000, cv0, cv6, cv3, cv1, cv2, cv4] 8 Tr.E) [cv8, 0xaaaaaa00aaaaaa00aaaaaa00aaaaaa00, cv6, cv3, cv1, cv2, cv4] 7 Tr.E)) [cv8, 0xaaaaaaaa00000000aaaaaaaa00000000, cv0, cv6, cv3, cv1, cv2, cv4] 8 (Tr.N (Tr.N (Tr.N Tr.E [cv8, 0xaaaaaaaaaaaaaaaa0000000000000000, cv0, cv6, cv3, cv1, cv2, cv4] 8 Tr.E) [cv8, cv0, cv0, cv6, cv3, cv1, cv2, cv4] 8 Tr.E) [cv8, cv0, 0xaaaaaaaaffffffffaaaaaaaaffffffff, cv6, cv3, cv1, cv2, cv4] 8 (Tr.N (Tr.N Tr.E [cv8, cv0, 0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0, cv6, cv3, cv1, cv2, cv4] 8 Tr.E) [cv8, cv0, 0xc8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8, cv3, cv1, cv2, cv4] 7 Tr.E))))
def u17 : Tr := Tr.N t15 [cv8, 0xffff0000ffff0000ffff0000ffff, cv0, cv6, cv3, cv1, cv4] 8 t16
def t18 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv8, cv0, 0xcccc0000cccc0000cccc0000cccc0000, cv6, cv3, cv1, cv2, cv4] 8 Tr.E) [cv8, cv0, 0xcccccccc00000000cccccccc00000000, cv6, cv3, cv1, cv2, cv4] 8 (Tr.N Tr.E [cv8, cv0, 0xcccccccccccccccc0000000000000000, cv6, cv3, cv1, cv2, cv4] 8 Tr.E)) [cv8, cv0, 0xcccccccccccccccccccccccc00000000, cv3, cv1, cv2, cv4] 7 (Tr.N (Tr.N Tr.E [cv8, cv0, cv6, cv6, cv3, cv1, cv2, cv4] 8 Tr.E) [cv8, cv0, cv6, 0xccccccccffffffffccccccccffffffff, cv3, cv1, cv2, cv4] 8 Tr.E)) [cv8, cv0, cv6, 0xe0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0, cv1, cv2, cv4] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv8, cv0, cv6, cv33, cv3, cv1, cv2, cv4] 8 Tr.E) [cv8, cv0, cv6, 0xf000f000f000f000f000f000f000f000, cv3, cv1, cv2, cv4] 8 (Tr.N Tr.E [cv8, cv0, cv6, cv54, cv3, cv1, cv2, cv4] 8 Tr.E)) [cv8, cv0, cv6, 0xf0f0f0f000000000f0f0f0f000000000, cv3, cv1, cv2, cv4] 8 (Tr.N (Tr.N Tr.E [cv8, cv0, cv6, 0xf0f0f0f0f0f00000f0f0f0f0f0f00000, cv1, cv2, cv4] 7 Tr.E) [cv8, cv0, cv6, 0xf0f0f0f0f0f0f0f00000000000000000, cv3, cv1, cv2, cv4] 8 Tr.E))) [cv8, cv0, cv6, cv3, cv3, cv1, cv2, cv4] 8 (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv8, cv0, cv6, cv3, 0xf0f0f0f0fffffffff0f0f0f0ffffffff, cv1, cv2, cv4] 8 Tr.E) [cv8, cv0, cv6, cv3, cv41, cv1, cv2, cv4] 8 (Tr.N Tr.E [cv8, cv0, cv6, cv3, 0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc, cv1, cv2, cv4] 8 Tr.E)) [cv8, cv0, cv6, cv3, cv22, cv1, cv2, cv4] 8 (Tr.N (Tr.N Tr.E [cv8, cv0, cv6, cv3, cv40, cv2, cv4] 7 Tr.E) [cv8, cv0, cv6, cv3, 0xff00ff0000000000ff00ff0000000000, cv1, cv2, cv4] 8 Tr.E)) [cv8, cv0, cv6, cv3, 0xff00ff00ff000000ff00ff00ff000000, cv2, cv4] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv8, cv0, cv6, cv3, 0xff00ff00ff00ff000000000000000000, cv1, cv2, cv4] 8 Tr.E) [cv8, cv0, cv6, cv3, cv1, cv1, cv2, cv4] 8 Tr.E) [cv8, cv0, cv6, cv3, cv1, 0xff00ff00ffffffffff00ff00ffffffff, cv2, cv4] 8 (Tr.N (Tr.N Tr.E [cv8, cv0, cv6, cv3, cv1, 0xffaa0000ffaa0000ffaa0000ffaa0000, cv4] 7 Tr.E) [cv8, cv0, cv6, cv3, cv1, cv58, cv2, cv4] 8 Tr.E))))
def t19 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv8, cv0, cv6, cv3, cv1, cv28, cv2, cv4] 8 Tr.E) [cv8, cv0, cv6, cv3, cv1, cv26, cv2, cv4] 8 (Tr.N Tr.E [cv8, cv0, cv6, cv3, cv1, 0xffff0000f0f00000ffff0000f0f00000, cv4] 7 Tr.E)) [cv8, cv0, cv6, cv3, cv1, cv17, cv4] 7 (Tr.N (Tr.N Tr.E [cv8, cv0, cv6, cv3, cv1, 0xffff0000ffff00000000000000000000, cv2, cv4] 8 Tr.E) [cv8, cv0, cv6, cv3, cv1, 0xffff0000ffff0000ffff000000000000, cv4] 7 Tr.E)) [cv8, cv0, cv6, cv3, cv1, cv2, cv2, cv4] 8 (Tr.N (Tr.N (Tr.N Tr.E [cv8, cv0, cv6, cv3, cv1, cv2, 0xffff0000ffffffffffff0000ffffffff, cv4] 8 Tr.E) [cv8, cv0, cv6, cv3, cv1, cv2, cv23, cv4] 8 Tr.E) [cv8, cv0, cv6, cv3, cv1, cv2, cv25, cv4] 8 (Tr.N (Tr.N Tr.E [cv8, cv0, cv6, cv3, cv1, cv2, cv50, cv4] 8 Tr.E) [cv8, cv0, cv6, cv3, cv1, cv2, 0xffffff00ffffff00ffffff00ffffff00, cv4] 8 Tr.E))) [cv8, cv0, cv6, cv3, cv1, cv2, 0xffffffff000000000000000000000000, cv4] 8 (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv8, cv0, cv6, cv3, cv1, cv2, cv5, cv4] 9 Tr.E) [cv8, cv0, cv6, cv3, cv1, cv2, cv13, cv4] 8 (Tr.N Tr.E [cv8, cv0, cv6, cv3, cv1, cv2, 0xffffffffcccccccc0000000000000000] 7 Tr.E)) [cv8, cv0, cv6, cv3, cv1, cv2, cv24, cv4] 8 (Tr.N (Tr.N Tr.E [cv8, cv0, cv6, cv3, cv1, cv2, 0xfffffffff0f0f0f0fffffffff0f0f0f0, cv4] 8 Tr.E) [cv8, cv0, cv6, cv3, cv1, cv2, cv27, cv4] 8 Tr.E)) [cv8, cv0, cv6, cv3, cv1, cv2, 0xffffffffffff00000000000000000000] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv8, cv0, cv6, cv3, cv1, cv2, 0xffffffffffff0000ffffffffffff0000, cv4] 8 Tr.E) [cv8, cv0, cv6, cv3, cv1, cv2, cv4] 9 Tr.E) [cv8, cv0, cv6, cv3, cv1, cv2, cv4, cv4] 8 (Tr.N (Tr.N Tr.E [cv8, cv0, cv6, cv3, cv1, cv2, cv4, 0xffffffffffffffff00000000ffffffff] 8 Tr.E) [cv8, cv0, cv6, cv3, cv1, cv2, cv4, cv15] 8 Tr.E))))
def u20 : Tr := Tr.N t18 [cv8, cv0, cv6, cv3, cv1, cv16, cv2, cv4] 8 t19
def u21 : Tr := Tr.N u17 [cv8, cv0, 0xcc00cc00cc00cc00cc00cc00cc00cc00, cv6, cv3, cv1, cv2, cv4] 8 u20
def t22 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv8, cv0, cv6, cv3, cv1, cv2, cv4, cv31] 8 Tr.E) [cv8, cv0, cv6, cv3, cv1, cv2, cv4, cv45] 8 (Tr.N Tr.E [cv8, cv0, cv6, cv3, cv1, cv2, cv4, cv35] 8 Tr.E)) [cv8, cv0, cv6, cv3, cv1, cv2, cv4, 0xffffffffffffffffffffffff00000000] 8 (Tr.N (Tr.N Tr.E [cv8, cv0, cv6, cv3, cv1, cv2, cv4, 0xffffffffffffffffffffffffffffffff] 8 Tr.E) [cv8, cv0, cv6, cv3, cv1, cv2, 0xffffffffffffffff00000000aaaaaaaa] 7 Tr.E)) [cv8, cv0, cv6, cv3, cv1, cv2, 0xffffffffffffffff00000000f0f0f0f0] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv8, cv0, cv6, cv3, cv1, cv2, 0xffffffffffffffff00000000ff00ff00] 7 Tr.E) [cv8, cv0, cv6, cv3, cv1, cv2, 0xffffffffffffffff8888888888888888] 7 (Tr.N Tr.E [cv8, cv0, cv6, cv3, cv1, cv2, 0xffffffffffffffffa0a0a0a0a0a0a0a0] 7 Tr.E)) [cv8, cv0, cv6, cv3, cv1, cv2, 0xffffffffffffffffaa00aa00aa00aa00] 7 (Tr.N (Tr.N Tr.E [cv8, cv0, cv6, cv3, cv1, cv2, 0xffffffffffffffffaaaa0000aaaa0000] 7 Tr.E) [cv8, cv0, cv6, cv3, cv1, cv2, cv57] 7 Tr.E))) [cv8, cv0, cv6, cv3, cv1, cv2, 0xfffffffffffffffff0f00000f0f00000] 7 (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv8, cv0, cv6, cv3, cv1, cv2, cv53] 7 Tr.E) [cv8, cv0, cv6, cv3, cv1, cv2, cv19] 7 (Tr.N Tr.E [cv8, cv0, cv6, cv3, cv1, 0xffff0000ffffaaaaffff0000ffffaaaa, cv4] 7 Tr.E)) [cv8, cv0, cv6, cv3, cv1, 0xffff0000ffffccccffff0000ffffcccc, cv4] 7 (Tr.N (Tr.N Tr.E [cv8, cv0, cv6, cv3, cv1, 0xffff8888ffff8888ffff8888ffff8888, cv4] 7 Tr.E) [cv8, cv0, cv6, cv3, cv1, 0xffffa0a0ffffa0a0ffffa0a0ffffa0a0, cv4] 7 Tr.E)) [cv8, cv0, cv6, cv3, cv1, cv55, cv4] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv8, cv0, cv6, cv3, cv1, 0xffffaaaaffffaaaaffff0000ffff0000, cv4] 7 Tr.E) [cv8, cv0, cv6, cv3, cv1, 0xffffc0c0ffffc0c0ffffc0c0ffffc0c0, cv4] 7 Tr.E) [cv8, cv0, cv6, cv3, cv1, 0xffffccccffffccccffff0000ffff0000, cv4] 7 (Tr.N (Tr.N Tr.E [cv8, cv0, cv6, cv3, cv1, cv51, cv4] 7 Tr.E) [cv8, cv0, cv6, cv3, 0xff88ff88ff88ff88ff88ff88ff88ff88, cv2, cv4] 7 Tr.E))))
def t23 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv8, cv0, cv6, cv3, 0xffc0ffc0ffc0ffc0ffc0ffc0ffc0ffc0, cv2, cv4] 7 Tr.E) [cv8, cv0, cv6, cv3, 0xffccffccff00ff00ffccffccff00ff00, cv2, cv4] 7 (Tr.N Tr.E [cv8, cv0, cv6, cv3, 0xffccffccffccffccff00ff00ff00ff00, cv2, cv4] 7 Tr.E)) [cv8, cv0, cv6, cv3, 0xfff0fff0ff00ff00fff0fff0ff00ff00, cv2, cv4] 7 (Tr.N (Tr.N Tr.E [cv8, cv0, cv6, cv3, cv2, cv56, cv4] 7 Tr.E) [cv8, cv0, cv6, cv3, cv2, 0xffffffffff00ff00ff00ff00ff00ff00, cv4] 7 Tr.E)) [cv8, cv0, cv6, 0xf0f0f0f0fff0fff0f0f0f0f0fff0fff0, cv1, cv2, cv4] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv8, cv0, cv6, 0xf8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8, cv1, cv2, cv4] 7 Tr.E) [cv8, cv0, cv6, cv38, cv1, cv2, cv4] 7 Tr.E) [cv8, cv0, cv6, 0xfcfcfcfcfcfcfcfcf0f0f0f0f0f0f0f0, cv1, cv2, cv4] 7 (Tr.N (Tr.N Tr.E [cv8, cv0, cv6, cv1, cv46, cv2, cv4] 7 Tr.E) [cv8, cv0, cv6, cv1, 0xfff0fff0fff0fff0f0f0f0f0f0f0f0f0, cv2, cv4] 7 Tr.E))) [cv8, cv0, cv6, cv1, cv2, cv20, cv4] 7 (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv8, cv0, cv6, cv1, cv2, 0xfffffffff0f0f0f0f0f0f0f0f0f0f0f0, cv4] 7 Tr.E) [cv8, cv0, cv47, cv3, cv1, cv2, cv4] 7 (Tr.N Tr.E [cv8, cv0, cv29, cv3, cv1, cv2, cv4] 7 Tr.E)) [cv8, cv0, cv3, cv1, cv14, cv2, cv4] 7 (Tr.N (Tr.N Tr.E [cv8, cv0, cv3, cv1, cv2, cv12, cv4] 7 Tr.E) [cv8, cv0, cv3, cv1, cv2, cv11, cv4] 7 Tr.E)) [cv8, cv0, cv1, cv21, cv32, cv4] 5 (Tr.N (Tr.N (Tr.N Tr.E [cv8, cv6, cv43, cv3, cv1, cv2, cv4] 7 Tr.E) [cv8, cv6, 0xeeeeeeeeeeeeeeeeaaaaaaaaaaaaaaaa, cv3, cv1, cv2, cv4] 7 Tr.E) [cv8, cv6, cv3, cv1, cv39, cv2, cv4] 7 (Tr.N (Tr.N Tr.E [cv8, cv6, cv3, cv1, cv2, cv30, cv4] 7 Tr.E) [cv8, cv6, cv3, cv1, cv2, 0xffffffffaaaaaaaaaaaaaaaaaaaaaaaa, cv4] 7 Tr.E))))
def u24 : Tr := Tr.N t22 [cv8, cv0, cv6, cv3, 0xffa0ffa0ffa0ffa0ffa0ffa0ffa0ffa0, cv2, cv4] 7 t23
def t25 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv8, cv3, cv1, cv2, cv30, cv12, cv4] 6 Tr.E) [cv8, cv3, cv1, cv52, cv21, cv4] 5 (Tr.N Tr.E [0xffffffff0000ffffffffffff, cv0, cv6, cv3, cv1, cv2, cv4] 7 Tr.E)) [0xffffffff33333333ffffffff, cv0, cv6, cv3, cv1, cv2, cv4] 7 (Tr.N (Tr.N Tr.E [0xffffffffffffffffffffffff, cv0, cv6, cv3, cv1, cv2, cv5, cv4] 8 Tr.E) [0xffffffffff000000ffffffffff, cv0, cv6, cv3, cv1, cv2, cv4] 7 Tr.E)) [0xf0f0f0f0f0f00000f0f0f0f0f0f, cv0, cv6, cv1, cv2, cv5, cv4] 7 (Tr.N (Tr.N (Tr.N Tr.E [0xf0fffffffff00000f0fffffffff, cv0, cv6, cv3, cv1, cv2, cv4] 7 Tr.E) [0x3333333333330000333333333333, cv0, cv3, cv1, cv2, cv5, cv4] 7 (Tr.N Tr.E [0x3333333333330000333333333333, cv0, cv3, cv1, cv2, cv13, cv4] 6 Tr.E)) [0x3333333333330000333333333333, cv3, cv1, cv2, cv30, cv5, cv4] 6 (Tr.N (Tr.N Tr.E [0xaaaaaaaaaaaa0000aaaaaaaaaaaa, cv6, cv3, cv1, cv2, cv5, cv4] 7 Tr.E) [0xf0f0f0f0f0f00000f0f0f0f0f0f0, cv0, cv6, cv1, cv2, cv5, cv4] 7 Tr.E))) [0xff00ff00ff000000ff00ff00ff00, cv0, cv6, cv3, cv2, cv5, cv4] 7 (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [0xffff0000ffffffffffffffffffff, cv0, cv6, cv3, cv1, cv2, cv5, cv4] 8 Tr.E) [0xffffffffffff0000ffffffffffff, cv0, cv6, cv3, cv1, cv2, cv5, cv4] 8 (Tr.N Tr.E [0xf000f000f000f0f0f0f0f0f0f0f0f, cv0, cv6, cv1, cv2, cv5, cv4] 7 Tr.E)) [0xf000f000f000f0f0f0f0f0f0f0f0f0, cv0, cv6, cv1, cv2, cv5, cv4] 7 (Tr.N (Tr.N Tr.E [0xff00ff00ff00ffffffffffffffffff, cv0, cv6, cv3, cv1, cv2, cv5, cv4] 8 Tr.E) [0x3030303030303030303030303030303, cv0, cv6, cv3, cv1, cv2, cv5, cv4] 8 Tr.E)) [0x3030303030303030f0f0f0f0f0f0f0f, cv0, cv6, cv1, cv2, cv5, cv4] 7 (Tr.N (Tr.N (Tr.N Tr.E [0x7070707070707070707070707070707, cv0, cv6, cv1, cv2, cv5, cv4] 7 Tr.E) [0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, cv10, cv0, cv6, cv1, cv2, cv5, cv4] 8 Tr.E) [0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, cv0, cv6, cv3, cv1, cv2, cv5, cv4] 8 (Tr.N (Tr.N Tr.E [0xe0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e, cv0, cv6, cv1, cv2, cv5, cv4] 7 Tr.E) [0xf000f000f000f000f000f000f000f00, cv10, cv0, cv6, cv1, cv2, cv5, cv4] 8 Tr.E))))
def t26 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [0xf000f00ff00ff000f000f00ff00ff00, cv0, cv6, cv3, cv2, cv5, cv4] 7 Tr.E) [0xf0f00000f0f00000f0f00000f0f0000, cv10, cv0, cv6, cv1, cv2, cv5, cv4] 8 (Tr.N Tr.E [0xf0f00000f0f00000f0f00000f0f0000, cv0, cv6, cv3, cv1, cv2, cv5, cv4] 8 Tr.E)) [0xf0f0f0f0f0f00000f0f0f0f0f0f0000, cv0, cv6, cv1, cv2, cv5, cv4] 7 (Tr.N (Tr.N Tr.E [cv10, cv10, cv0, cv6, cv1, cv2, cv5, cv4] 8 Tr.E) [cv10, cv9, cv49, cv1, cv2, cv5, cv4] 7 Tr.E)) [cv10, cv9, cv0, cv6, cv1, cv2, cv5, cv4] 8 (Tr.N (Tr.N (Tr.N Tr.E [cv10, cv9, cv0, cv3, cv1, cv2, cv5, cv4] 8 Tr.E) [cv10, cv9, cv0, cv1, cv2, cv5, cv4] 8 Tr.E) [cv10, 0x88888888888888888888888888888888, cv0, cv6, cv1, cv2, cv5, cv4] 8 (Tr.N (Tr.N Tr.E [cv10, cv34, cv0, cv6, cv1, cv2, cv5, cv4] 8 Tr.E) [cv10, cv48, cv6, cv1, cv2, cv5, cv4] 7 Tr.E))) [cv10, cv37, cv0, cv6, cv1, cv2, cv5, cv4] 8 (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv10, 0xaaaa0000aaaa0000aaaa0000aaaa0000, cv0, cv6, cv1, cv2, cv5, cv4] 8 Tr.E) [cv10, 0xaaaaaa00aaaaaa00aaaaaa00aaaaaa00, cv6, cv1, cv2, cv5, cv4] 7 (Tr.N Tr.E [cv10, 0xaaaaaaaa00000000aaaaaaaa00000000, cv0, cv6, cv1, cv2, cv5, cv4] 8 Tr.E)) [cv10, 0xaaaaaaaaaaaaaaaa0000000000000000, cv0, cv6, cv1, cv2, cv5, cv4] 8 (Tr.N (Tr.N Tr.E [cv10, cv0, cv0, cv6, cv1, cv2, cv5, cv4] 8 Tr.E) [cv10, cv0, 0xafafafafafafafafafafafafafafafaf, cv6, cv1, cv2, cv5, cv4] 8 Tr.E)) [cv10, cv0, cv6, cv33, cv1, cv2, cv5, cv4] 8 (Tr.N (Tr.N (Tr.N Tr.E [cv10, cv0, cv6, 0xf000f000f000f000f000f000f000f000, cv1, cv2, cv5, cv4] 8 Tr.E) [cv10, cv0, cv6, cv54, cv1, cv2, cv5, cv4] 8 Tr.E) [cv10, cv0, cv6, cv3, cv1, cv2, cv5, cv4] 9 (Tr.N (Tr.N Tr.E [cv10, cv0, cv6, cv41, cv1, cv2, cv5, cv4] 8 Tr.E) [cv10, cv0, cv6, cv22, cv1, cv2, cv5, cv4] 8 Tr.E))))
def u27 : Tr := Tr.N t25 [0xf000f000f000f000f000f000f000f00, cv0, cv6, cv3, cv1, cv2, cv5, cv4] 8 t26
def u28 : Tr := Tr.N u24 [cv8, cv6, cv3, cv1, cv30, cv25, cv4] 6 u27
def u29 : Tr := Tr.N u21 [cv8, cv0, cv6, cv3, cv1, cv2, cv4, 0xffffffffffffffffcccccccccccccccc] 8 u28
def u30 : Tr := Tr.N u14 [0x5f5f5f5f000000005f5f5f5f, cv0, cv6, cv3, cv1, cv2, cv4] 7 u29
def t31 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv10, cv0, cv6, cv40, cv2, cv5, cv4] 7 Tr.E) [cv10, cv0, cv6, 0xff00ff0000000000ff00ff0000000000, cv1, cv2, cv5, cv4] 8 (Tr.N Tr.E [cv10, cv0, cv6, 0xff00ff00ff000000ff00ff00ff000000, cv2, cv5, cv4] 7 Tr.E)) [cv10, cv0, cv6, 0xff00ff00ff00ff000000000000000000, cv1, cv2, cv5, cv4] 8 (Tr.N (Tr.N Tr.E [cv10, cv0, cv6, 0xff00ff00ff00ff000f000f000f000f00, cv2, cv5, cv4] 7 Tr.E) [cv10, cv0, cv6, cv1, cv1, cv2, cv5, cv4] 8 Tr.E)) [cv10, cv0, cv6, cv1, 0xff0f0000ff0f0000ff0f0000ff0f0000, cv5, cv4] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv10, cv0, cv6, cv1, 0xff0fff0fff0fff0fff0fff0fff0fff0f, cv2, cv5, cv4] 8 Tr.E) [cv10, cv0, cv6, cv1, 0xffaa0000ffaa0000ffaa0000ffaa0000, cv5, cv4] 7 (Tr.N Tr.E [cv10, cv0, cv6, cv1, cv58, cv2, cv5, cv4] 8 Tr.E)) [cv10, cv0, cv6, cv1, cv16, cv2, cv5, cv4] 8 (Tr.N (Tr.N Tr.E [cv10, cv0, cv6, cv1, cv28, cv2, cv5, cv4] 8 Tr.E) [cv10, cv0, cv6, cv1, cv26, cv2, cv5, cv4] 8 Tr.E))) [cv10, cv0, cv6, cv1, 0xffff0000f0f00000ffff0000f0f00000, cv5, cv4] 7 (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv10, cv0, cv6, cv1, cv17, cv5, cv4] 7 Tr.E) [cv10, cv0, cv6, cv1, 0xffff0000ffff0000ffff000000000000, cv5, cv4] 7 (Tr.N Tr.E [cv10, cv0, cv6, cv1, cv2, cv2, cv5, cv4] 8 Tr.E)) [cv10, cv0, cv6, cv1, cv2, 0xffff0f0fffff0f0fffff0f0fffff0f0f, cv5, cv4] 8 (Tr.N (Tr.N Tr.E [cv10, cv0, cv6, cv1, cv2, cv23, cv5, cv4] 8 Tr.E) [cv10, cv0, cv6, cv1, cv2, cv25, cv5, cv4] 8 Tr.E)) [cv10, cv0, cv6, cv1, cv2, cv50, cv5, cv4] 8 (Tr.N (Tr.N (Tr.N Tr.E [cv10, cv0, cv6, cv1, cv2, 0xffffff00ffffff00ffffff00ffffff00, cv5, cv4] 8 Tr.E) [cv10, cv0, cv6, cv1, cv2, cv5, cv27, cv4] 8 Tr.E) [cv10, cv0, cv6, cv1, cv2, cv5, 0xffffffffffff0000ffffffffffff0000, cv4] 8 (Tr.N (Tr.N Tr.E [cv10, cv0, cv6, cv1, cv2, cv5, cv4] 9 Tr.E) [cv10, cv0, cv6, cv1, cv2, cv5, cv4, cv45] 8 Tr.E))))
def t32 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv10, cv0, cv6, cv1, cv2, cv5, 0xffffffffffffffff8888888888888888] 7 Tr.E) [cv10, cv0, cv6, cv1, cv2, cv5, 0xffffffffffffffffa0a0a0a0a0a0a0a0] 7 (Tr.N Tr.E [cv10, cv0, cv6, cv1, cv2, cv5, 0xffffffffffffffffaa00aa00aa00aa00] 7 Tr.E)) [cv10, cv0, cv6, cv1, cv2, cv5, 0xffffffffffffffffaaaa0000aaaa0000] 7 (Tr.N (Tr.N Tr.E [cv10, cv0, cv6, cv1, cv2, cv5, cv57] 7 Tr.E) [cv10, cv0, cv6, cv1, cv2, cv5, 0xfffffffffffffffff0f00000f0f00000] 7 Tr.E)) [cv10, cv0, cv6, cv1, cv2, cv5, cv53] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv10, cv0, cv6, cv1, cv2, cv5, cv19] 7 Tr.E) [cv10, cv0, cv6, cv1, cv2, 0xffffffff0f000f00ffffffff0f000f00, cv4] 7 (Tr.N Tr.E [cv10, cv0, cv6, cv1, cv2, cv59, cv4] 7 Tr.E)) [cv10, cv0, cv6, cv1, cv2, 0xffffffffa0a0a0a0ffffffffa0a0a0a0, cv4] 7 (Tr.N (Tr.N Tr.E [cv10, cv0, cv6, cv1, cv2, 0xffffffffaa00aa00ffffffffaa00aa00, cv4] 7 Tr.E) [cv10, cv0, cv6, cv1, cv2, 0xffffffffc0c0c0c0ffffffffc0c0c0c0, cv4] 7 Tr.E))) [cv10, cv0, cv6, cv1, cv2, 0xffffffffcc00cc00ffffffffcc00cc00, cv4] 7 (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv10, cv0, cv6, cv1, cv2, 0xffffffffccccccccffffffff00000000, cv4] 7 Tr.E) [cv10, cv0, cv6, cv1, cv2, cv36, cv4] 7 (Tr.N Tr.E [cv10, cv0, 0xcfcccfcccfcccfcccfcccfcccfcccfcc, cv1, cv2, cv5, cv4] 7 Tr.E)) [cv10, cv0, cv47, cv1, cv2, cv5, cv4] 7 (Tr.N (Tr.N Tr.E [cv10, cv0, cv29, cv1, cv2, cv5, cv4] 7 Tr.E) [cv10, cv0, cv1, cv14, cv2, cv5, cv4] 7 Tr.E)) [cv10, cv0, cv1, cv2, cv12, cv5, cv4] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv10, cv0, cv1, cv2, cv12, cv13, cv4] 6 Tr.E) [cv10, cv0, cv1, cv2, cv5, cv11, cv4] 7 Tr.E) [cv10, cv1, cv2, cv30, cv12, cv5, cv4] 6 (Tr.N (Tr.N Tr.E [cv10, cv1, cv2, cv44, cv18, cv4] 5 Tr.E) [0xf0f0f0f0f0f0f0fffffffffffffffff, cv0, cv6, cv3, cv1, cv2, cv5, cv4] 8 Tr.E))))
def u33 : Tr := Tr.N t31 [cv10, cv0, cv6, cv1, cv2, cv5, cv4, 0xffffffffffffffffffffffffffffffff] 8 t32
def t34 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [0xf0f0f0fffffffff0f0f0f0fffffffff, cv0, cv6, cv3, cv1, cv2, cv5, cv4] 8 Tr.E) [0x11111111111111111111111111111111, cv0, cv6, cv3, cv1, cv2, cv5, cv4] 8 (Tr.N Tr.E [0x11111111111111115555555555555555, cv6, cv3, cv1, cv2, cv5, cv4] 7 Tr.E)) [0x13131313131313131313131313131313, cv0, cv3, cv1, cv2, cv5, cv4] 7 (Tr.N (Tr.N Tr.E [0x1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f, cv0, cv6, cv1, cv2, cv5, cv4] 7 Tr.E) [0x22222222222222222222222222222222, cv9, cv0, cv3, cv1, cv2, cv5, cv4] 8 Tr.E)) [0x22222222222222222222222222222222, cv0, cv6, cv3, cv1, cv2, cv5, cv4] 8 (Tr.N (Tr.N (Tr.N Tr.E [0x2222222222222222aaaaaaaaaaaaaaaa, cv6, cv3, cv1, cv2, cv5, cv4] 7 Tr.E) [0x2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a, cv6, cv3, cv1, cv2, cv5, cv4] 7 (Tr.N Tr.E [0x30303030303030303030303030303030, cv9, cv0, cv3, cv1, cv2, cv5, cv4] 8 Tr.E)) [0x30303030303030303030303030303030, cv0, cv6, cv3, cv1, cv2, cv5, cv4] 8 (Tr.N (Tr.N Tr.E [0x3030303030303030f0f0f0f0f0f0f0f0, cv0, cv6, cv1, cv2, cv5, cv4] 7 Tr.E) [0x32323232323232323232323232323232, cv0, cv3, cv1, cv2, cv5, cv4] 7 Tr.E))) [0x33003300330033003300330033003300, cv9, cv0, cv3, cv1, cv2, cv5, cv4] 8 (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [0x33003300330033003300330033003300, cv0, cv6, cv3, cv1, cv2, cv5, cv4] 8 Tr.E) [0x3300330033003300ff00ff00ff00ff00, cv0, cv6, cv3, cv2, cv5, cv4] 7 (Tr.N Tr.E [0x33003300ff00ff0033003300ff00ff00, cv0, cv6, cv3, cv2, cv5, cv4] 7 Tr.E)) [0x33330000333300003333000033330000, cv9, cv0, cv3, cv1, cv2, cv5, cv4] 8 (Tr.N (Tr.N Tr.E [0x33330000333300003333000033330000, cv0, cv6, cv3, cv1, cv2, cv5, cv4] 8 Tr.E) [0x3333000033330000ffff0000ffff0000, cv0, cv6, cv3, cv1, cv5, cv4] 7 Tr.E)) [0x33333333000000003333333300000000, cv9, cv0, cv3, cv1, cv2, cv5, cv4] 8 (Tr.N (Tr.N (Tr.N Tr.E [0x33333333000000003333333300000000, cv0, cv6, cv3, cv1, cv2, cv5, cv4] 8 Tr.E) [0x3333333300000000ffffffff00000000, cv0, cv6, cv3, cv1, cv2, cv4] 7 Tr.E) [0x33333333333333330000000000000000, cv9, cv0, cv3, cv1, cv2, cv5, cv4] 8 (Tr.N (Tr.N Tr.E [0x33333333333333330000000000000000, cv0, cv6, cv3, cv1, cv2, cv5, cv4] 8 Tr.E) [0x33333333333333333333333300000000, cv0, cv3, cv1, cv2, cv5, cv4] 7 Tr.E))))
def t35 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv9, cv49, cv0, cv3, cv1, cv2, cv5, cv4] 8 Tr.E) [cv9, cv49, cv3, cv1, cv2, cv5, cv4] 8 (Tr.N Tr.E [cv9, 0x88888888888888888888888888888888, cv0, cv3, cv1, cv2, cv5, cv4] 8 Tr.E)) [cv9, cv34, cv0, cv3, cv1, cv2, cv5, cv4] 8 (Tr.N (Tr.N Tr.E [cv9, cv48, cv3, cv1, cv2, cv5, cv4] 7 Tr.E) [cv9, cv37, cv0, cv3, cv1, cv2, cv5, cv4] 8 Tr.E)) [cv9, 0xaaaa0000aaaa0000aaaa0000aaaa0000, cv0, cv3, cv1, cv2, cv5, cv4] 8 (Tr.N (Tr.N (Tr.N Tr.E [cv9, 0xaaaaaa00aaaaaa00aaaaaa00aaaaaa00, cv3, cv1, cv2, cv5, cv4] 7 Tr.E) [cv9, 0xaaaaaaaa00000000aaaaaaaa00000000, cv0, cv3, cv1, cv2, cv5, cv4] 8 Tr.E) [cv9, 0xaaaaaaaaaaaaaaaa0000000000000000, cv0, cv3, cv1, cv2, cv5, cv4] 8 (Tr.N (Tr.N Tr.E [cv9, cv0, cv0, cv3, cv1, cv2, cv5, cv4] 8 Tr.E) [cv9, cv0, 0xbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb, cv3, cv1, cv2, cv5, cv4] 8 Tr.E))) [cv9, cv0, 0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0, cv3, cv1, cv2, cv5, cv4] 8 (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv9, cv0, 0xcc00cc00cc00cc00cc00cc00cc00cc00, cv3, cv1, cv2, cv5, cv4] 8 Tr.E) [cv9, cv0, 0xcccc0000cccc0000cccc0000cccc0000, cv3, cv1, cv2, cv5, cv4] 8 (Tr.N Tr.E [cv9, cv0, 0xcccccccc00000000cccccccc00000000, cv3, cv1, cv2, cv5, cv4] 8 Tr.E)) [cv9, cv0, 0xcccccccccccccccc0000000000000000, cv3, cv1, cv2, cv5, cv4] 8 (Tr.N (Tr.N Tr.E [cv9, cv0, cv6, cv3, cv1, cv2, cv5, cv4] 9 Tr.E) [cv9, cv0, 0xe0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0, cv1, cv2, cv5, cv4] 7 Tr.E)) [cv9, cv0, cv33, cv3, cv1, cv2, cv5, cv4] 8 (Tr.N (Tr.N (Tr.N Tr.E [cv9, cv0, 0xf000f000f000f000f000f000f000f000, cv3, cv1, cv2, cv5, cv4] 8 Tr.E) [cv9, cv0, cv54, cv3, cv1, cv2, cv5, cv4] 8 Tr.E) [cv9, cv0, 0xf0f0f0f000000000f0f0f0f000000000, cv3, cv1, cv2, cv5, cv4] 8 (Tr.N (Tr.N Tr.E [cv9, cv0, 0xf0f0f0f0f0f00000f0f0f0f0f0f00000, cv1, cv2, cv5, cv4] 7 Tr.E) [cv9, cv0, 0xf0f0f0f0f0f0f0f00000000000000000, cv3, cv1, cv2, cv5, cv4] 8 Tr.E))))
def u36 : Tr := Tr.N t34 [cv9, cv9, cv0, cv3, cv1, cv2, cv5, cv4] 8 t35
def u37 : Tr := Tr.N u33 [0xf0f0f0f0f0fffff0f0f0f0f0f0fffff, cv0, cv6, cv1, cv2, cv5, cv4] 7 u36
def t38 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv9, cv0, cv3, 0xf3f3f3f3f3f3f3f3f3f3f3f3f3f3f3f3, cv1, cv2, cv5, cv4] 8 Tr.E) [cv9, cv0, cv3, cv41, cv1, cv2, cv5, cv4] 8 (Tr.N Tr.E [cv9, cv0, cv3, 0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc, cv1, cv2, cv5, cv4] 8 Tr.E)) [cv9, cv0, cv3, cv22, cv1, cv2, cv5, cv4] 8 (Tr.N (Tr.N Tr.E [cv9, cv0, cv3, 0xff003300ff003300ff003300ff003300, cv2, cv5, cv4] 7 Tr.E) [cv9, cv0, cv3, cv40, cv2, cv5, cv4] 7 Tr.E)) [cv9, cv0, cv3, 0xff00ff0000000000ff00ff0000000000, cv1, cv2, cv5, cv4] 8 (Tr.N (Tr.N (Tr.N Tr.E [cv9, cv0, cv3, 0xff00ff00ff000000ff00ff00ff000000, cv2, cv5, cv4] 7 Tr.E) [cv9, cv0, cv3, 0xff00ff00ff00ff000000000000000000, cv1, cv2, cv5, cv4] 8 (Tr.N Tr.E [cv9, cv0, cv3, cv1, cv1, cv2, cv5, cv4] 8 Tr.E)) [cv9, cv0, cv3, cv1, 0xff330000ff330000ff330000ff330000, cv5, cv4] 7 (Tr.N (Tr.N Tr.E [cv9, cv0, cv3, cv1, 0xff33ff33ff33ff33ff33ff33ff33ff33, cv2, cv5, cv4] 8 Tr.E) [cv9, cv0, cv3, cv1, 0xffaa0000ffaa0000ffaa0000ffaa0000, cv5, cv4] 7 Tr.E))) [cv9, cv0, cv3, cv1, cv58, cv2, cv5, cv4] 8 (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv9, cv0, cv3, cv1, cv16, cv2, cv5, cv4] 8 Tr.E) [cv9, cv0, cv3, cv1, cv28, cv2, cv5, cv4] 8 (Tr.N Tr.E [cv9, cv0, cv3, cv1, cv26, cv2, cv5, cv4] 8 Tr.E)) [cv9, cv0, cv3, cv1, 0xffff000033330000ffff000033330000, cv5, cv4] 7 (Tr.N (Tr.N Tr.E [cv9, cv0, cv3, cv1, 0xffff0000f0f00000ffff0000f0f00000, cv5, cv4] 7 Tr.E) [cv9, cv0, cv3, cv1, cv17, cv5, cv4] 7 Tr.E)) [cv9, cv0, cv3, cv1, 0xffff0000ffff00000000000000000000, cv2, cv5, cv4] 8 (Tr.N (Tr.N (Tr.N Tr.E [cv9, cv0, cv3, cv1, 0xffff0000ffff0000ffff000000000000, cv5, cv4] 7 Tr.E) [cv9, cv0, cv3, cv1, cv2, cv2, cv5, cv4] 8 Tr.E) [cv9, cv0, cv3, cv1, cv2, 0xffff333300000000ffff333300000000, cv4] 7 (Tr.N (Tr.N Tr.E [cv9, cv0, cv3, cv1, cv2, 0xffff3333ffff3333ffff3333ffff3333, cv5, cv4] 8 Tr.E) [cv9, cv0, cv3, cv1, cv2, cv23, cv5, cv4] 8 Tr.E))))
def t39 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv9, cv0, cv3, cv1, cv2, 0xfffff0f000000000fffff0f000000000, cv4] 7 Tr.E) [cv9, cv0, cv3, cv1, cv2, cv50, cv5, cv4] 8 (Tr.N Tr.E [cv9, cv0, cv3, cv1, cv2, 0xffffff0000000000ffffff0000000000, cv4] 7 Tr.E)) [cv9, cv0, cv3, cv1, cv2, 0xffffff00ffffff00ffffff00ffffff00, cv5, cv4] 8 (Tr.N (Tr.N Tr.E [cv9, cv0, cv3, cv1, cv2, 0xffffffff000000000000000000000000, cv5, cv4] 8 Tr.E) [cv9, cv0, cv3, cv1, cv2, 0xffffffff00000000cccccccc00000000, cv4] 7 Tr.E)) [cv9, cv0, cv3, cv1, cv2, cv42, cv4] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv9, cv0, cv3, cv1, cv2, cv5, cv5, cv4] 8 Tr.E) [cv9, cv0, cv3, cv1, cv2, cv5, 0xffffffff33333333ffffffff33333333, cv4] 8 Tr.E) [cv9, cv0, cv3, cv1, cv2, cv5, cv13, cv4] 8 (Tr.N (Tr.N Tr.E [cv9, cv0, cv3, cv1, cv2, cv5, 0xffffffffcccccccc0000000000000000] 7 Tr.E) [cv9, cv0, cv3, cv1, cv2, cv5, cv24, cv4] 8 Tr.E))) [cv9, cv0, cv3, cv1, cv2, cv5, 0xfffffffff0f0f0f0fffffffff0f0f0f0, cv4] 8 (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv9, cv0, cv3, cv1, cv2, cv5, cv27, cv4] 8 Tr.E) [cv9, cv0, cv3, cv1, cv2, cv5, 0xffffffffffff00000000000000000000] 7 (Tr.N Tr.E [cv9, cv0, cv3, cv1, cv2, cv5, 0xffffffffffff0000ffffffffffff0000, cv4] 8 Tr.E)) [cv9, cv0, cv3, cv1, cv2, cv5, cv4] 9 (Tr.N (Tr.N Tr.E [cv9, cv0, cv3, cv1, cv2, cv5, cv4, cv4] 8 Tr.E) [cv9, cv0, cv3, cv1, cv2, cv5, cv4, 0xffffffffffffffff3333333333333333] 8 Tr.E)) [cv9, cv0, cv3, cv1, cv2, cv5, cv4, cv15] 8 (Tr.N (Tr.N (Tr.N Tr.E [cv9, cv0, cv3, cv1, cv2, cv5, cv4, 0xffffffffffffffffcccccccccccccccc] 8 Tr.E) [cv9, cv0, cv3, cv1, cv2, cv5, cv4, cv31] 8 Tr.E) [cv9, cv0, cv3, cv1, cv2, cv5, cv4, cv45] 8 (Tr.N (Tr.N Tr.E [cv9, cv0, cv3, cv1, cv2, cv5, cv4, cv35] 8 Tr.E) [cv9, cv0, cv3, cv1, cv2, cv5, cv4, 0xffffffffffffffffffffffff00000000] 8 Tr.E))))
def u40 : Tr := Tr.N t38 [cv9, cv0, cv3, cv1, cv2, cv25, cv5, cv4] 8 t39
def t41 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv9, cv0, cv3, cv1, cv2, cv5, 0xffffffffffffffff3333000033330000] 7 Tr.E) [cv9, cv0, cv3, cv1, cv2, cv5, 0xffffffffffffffff8888888888888888] 7 (Tr.N Tr.E [cv9, cv0, cv3, cv1, cv2, cv5, 0xffffffffffffffffa0a0a0a0a0a0a0a0] 7 Tr.E)) [cv9, cv0, cv3, cv1, cv2, cv5, 0xffffffffffffffffaa00aa00aa00aa00] 7 (Tr.N (Tr.N Tr.E [cv9, cv0, cv3, cv1, cv2, cv5, 0xffffffffffffffffaaaa0000aaaa0000] 7 Tr.E) [cv9, cv0, cv3, cv1, cv2, cv5, cv57] 7 Tr.E)) [cv9, cv0, cv3, cv1, cv2, cv5, 0xfffffffffffffffff0f00000f0f00000] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv9, cv0, cv3, cv1, cv2, cv5, cv53] 7 Tr.E) [cv9, cv0, cv3, cv1, cv2, cv5, cv19] 7 (Tr.N Tr.E [cv9, cv0, cv3, cv1, cv2, cv59, cv4] 7 Tr.E)) [cv9, cv0, cv3, cv1, cv2, 0xffffffffa0a0a0a0ffffffffa0a0a0a0, cv4] 7 (Tr.N (Tr.N Tr.E [cv9, cv0, cv3, cv1, cv2, 0xffffffffaa00aa00ffffffffaa00aa00, cv4] 7 Tr.E) [cv9, cv0, cv3, cv1, cv2, 0xffffffffc0c0c0c0ffffffffc0c0c0c0, cv4] 7 Tr.E))) [cv9, cv0, cv3, cv1, cv2, 0xffffffffcc00cc00ffffffffcc00cc00, cv4] 7 (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv9, cv0, cv3, cv1, cv2, 0xffffffffccccccccffffffff00000000, cv4] 7 Tr.E) [cv9, cv0, cv3, cv1, cv2, cv36, cv4] 7 (Tr.N Tr.E [cv9, cv0, cv3, cv1, 0xffff8888ffff8888ffff8888ffff8888, cv5, cv4] 7 Tr.E)) [cv9, cv0, cv3, cv1, 0xffffa0a0ffffa0a0ffffa0a0ffffa0a0, cv5, cv4] 7 (Tr.N (Tr.N Tr.E [cv9, cv0, cv3, cv1, cv55, cv5, cv4] 7 Tr.E) [cv9, cv0, cv3, cv1, 0xffffaaaaffffaaaaffff0000ffff0000, cv5, cv4] 7 Tr.E)) [cv9, cv0, cv3, cv1, 0xffffc0c0ffffc0c0ffffc0c0ffffc0c0, cv5, cv4] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv9, cv0, cv3, cv1, 0xffffccccffffccccffff0000ffff0000, cv5, cv4] 7 Tr.E) [cv9, cv0, cv3, cv1, cv5, cv51, cv4] 7 Tr.E) [cv9, cv0, cv3, 0xff88ff88ff88ff88ff88ff88ff88ff88, cv2, cv5, cv4] 7 (Tr.N (Tr.N Tr.E [cv9, cv0, cv3, 0xffa0ffa0ffa0ffa0ffa0ffa0ffa0ffa0, cv2, cv5, cv4] 7 Tr.E) [cv9, cv0, cv3, 0xffc0ffc0ffc0ffc0ffc0ffc0ffc0ffc0, cv2, cv5, cv4] 7 Tr.E))))
def t42 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv9, cv0, cv3, 0xffccffccffccffccff00ff00ff00ff00, cv2, cv5, cv4] 7 Tr.E) [cv9, cv0, cv3, 0xfff0fff0ff00ff00fff0fff0ff00ff00, cv2, cv5, cv4] 7 (Tr.N Tr.E [cv9, cv0, cv3, cv2, cv56, cv5, cv4] 7 Tr.E)) [cv9, cv0, cv3, cv2, cv5, 0xffffffffff00ff00ff00ff00ff00ff00, cv4] 7 (Tr.N (Tr.N Tr.E [cv9, cv0, 0xf3f0f3f0f3f0f3f0f3f0f3f0f3f0f3f0, cv1, cv2, cv5, cv4] 7 Tr.E) [cv9, cv0, 0xf8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8, cv1, cv2, cv5, cv4] 7 Tr.E)) [cv9, cv0, cv38, cv1, cv2, cv5, cv4] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv9, cv0, 0xfcfcfcfcfcfcfcfcf0f0f0f0f0f0f0f0, cv1, cv2, cv5, cv4] 7 Tr.E) [cv9, cv0, cv1, cv46, cv2, cv5, cv4] 7 Tr.E) [cv9, cv0, cv1, 0xfff0fff0fff0fff0f0f0f0f0f0f0f0f0, cv2, cv5, cv4] 7 (Tr.N (Tr.N Tr.E [cv9, cv0, cv1, cv2, cv20, cv5, cv4] 7 Tr.E) [cv9, cv0, cv1, cv2, cv5, 0xfffffffff0f0f0f0f0f0f0f0f0f0f0f0, cv4] 7 Tr.E))) [cv9, cv43, cv3, cv1, cv2, cv5, cv4] 7 (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv9, 0xeeeeeeeeeeeeeeeeaaaaaaaaaaaaaaaa, cv3, cv1, cv2, cv5, cv4] 7 Tr.E) [cv9, cv3, cv1, cv39, cv2, cv5, cv4] 7 (Tr.N Tr.E [cv9, cv3, cv1, cv2, cv30, cv5, cv4] 7 Tr.E)) [cv9, cv3, cv1, cv2, cv5, 0xffffffffaaaaaaaaaaaaaaaaaaaaaaaa, cv4] 7 (Tr.N (Tr.N Tr.E [cv9, cv3, cv1, cv30, cv25, cv5, cv4] 6 Tr.E) [cv9, cv1, cv2, cv44, 0xfffffffff0f0f0f0fffff0f0f0f0f0f0, cv4] 5 Tr.E)) [0x333333333333333333333333ffffffff, cv0, cv3, cv1, cv2, cv5, cv4] 7 (Tr.N (Tr.N (Tr.N Tr.E [0x3333333333333333ffffffffffffffff, cv0, cv6, cv3, cv1, cv2, cv5, cv4] 8 Tr.E) [0x33333333ffffffff33333333ffffffff, cv0, cv6, cv3, cv1, cv2, cv5, cv4] 8 Tr.E) [0x3333ffff3333ffff3333ffff3333ffff, cv0, cv6, cv3, cv1, cv2, cv5, cv4] 8 (Tr.N (Tr.N Tr.E [0x33ff33ff0000000033ff33ff00000000, cv0, cv6, cv3, cv1, cv2, cv4] 7 Tr.E) [0x33ff33ff33ff33ff33ff33ff33ff33ff, cv0, cv6, cv3, cv1, cv2, cv5, cv4] 8 Tr.E))))
def u43 : Tr := Tr.N t41 [cv9, cv0, cv3, 0xffccffccff00ff00ffccffccff00ff00, cv2, cv5, cv4] 7 t42
def u44 : Tr := Tr.N u40 [cv9, cv0, cv3, cv1, cv2, cv5, cv4, 0xffffffffffffffffffffffffffffffff] 8 u43
def u45 : Tr := Tr.N u37 [cv9, cv0, cv3, cv3, cv1, cv2, cv5, cv4] 8 u44
def t46 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [0x3f003f003f003f003f003f003f003f00, cv0, cv6, cv3, cv2, cv5, cv4] 7 Tr.E) [0x3f3f00003f3f00003f3f00003f3f0000, cv0, cv6, cv3, cv1, cv5, cv4] 7 (Tr.N Tr.E [0x3f3f3f3f000000003f3f3f3f00000000, cv0, cv6, cv3, cv1, cv2, cv4] 7 Tr.E)) [0x3f3f3f3f3f3f3f3f0000000000000000, cv0, cv6, cv3, cv1, cv2, cv5] 7 (Tr.N (Tr.N Tr.E [0x3f3f3f3f3f3f3f3f3f3f3f3f3f3f3f3f, cv0, cv6, cv3, cv1, cv2, cv5, cv4] 8 Tr.E) [0x70707070707070707070707070707070, cv0, cv6, cv1, cv2, cv5, cv4] 7 Tr.E)) [0x77007700770077007700770077007700, cv0, cv6, cv3, cv2, cv5, cv4] 7 (Tr.N (Tr.N (Tr.N Tr.E [0x77770000777700007777000077770000, cv0, cv6, cv3, cv1, cv5, cv4] 7 Tr.E) [0x77777777777777777777777777777777, cv0, cv6, cv3, cv1, cv2, cv5, cv4] 8 (Tr.N Tr.E [0x80808080808080808080808080808080, cv0, cv6, cv3, cv1, cv2, cv5, cv4] 8 Tr.E)) [0x88008800880088008800880088008800, cv0, cv6, cv3, cv1, cv2, cv5, cv4] 8 (Tr.N (Tr.N Tr.E [0x88880000888800008888000088880000, cv0, cv6, cv3, cv1, cv2, cv5, cv4] 8 Tr.E) [0x88888888888888888888888888888888, cv34, cv6, cv3, cv1, cv2, cv5, cv4] 8 Tr.E))) [0x88888888888888888888888888888888, cv0, cv6, cv3, cv1, cv2, cv5, cv4] 9 (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [0x88888888888888888888888888888888, cv0, cv6, cv3, cv1, cv2, cv5, 0xffffffffffffffff8888888888888888] 8 Tr.E) [0x88888888888888888888888888888888, cv0, cv6, cv3, cv1, cv2, cv59, cv4] 8 (Tr.N Tr.E [0x88888888888888888888888888888888, cv0, cv6, 0xf8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8, cv1, cv2, cv5, cv4] 8 Tr.E)) [0x88888888888888888888888888888888, cv0, cv33, cv3, cv1, cv2, cv5, cv4] 8 (Tr.N (Tr.N Tr.E [0x88888888888888888888888888888888, cv43, cv3, cv1, cv2, cv5, cv4] 7 Tr.E) [0x8888888888888888ffffffffffffffff, cv0, cv6, cv3, cv1, cv2, cv5] 7 Tr.E)) [0x88888888ffffffff88888888ffffffff, cv0, cv6, cv3, cv1, cv2, cv4] 7 (Tr.N (Tr.N (Tr.N Tr.E [0x8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f, cv0, cv6, cv1, cv2, cv5, cv4] 7 Tr.E) [0xa000a000a000a000a000a000a000a000, cv0, cv6, cv3, cv1, cv2, cv5, cv4] 8 Tr.E) [0xa0a00000a0a00000a0a00000a0a00000, cv0, cv6, cv3, cv1, cv2, cv5, cv4] 8 (Tr.N (Tr.N Tr.E [0xa0a0a0a000000000a0a0a0a000000000, cv0, cv6, cv3, cv1, cv2, cv5, cv4] 8 Tr.E) [0xa0a0a0a0a0a0a0a00000000000000000, cv0, cv6, cv3, cv1, cv2, cv5, cv4] 8 Tr.E))))
def t47 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv34, cv0, cv6, cv3, cv1, cv2, cv5, cv4] 9 Tr.E) [cv34, cv0, cv6, cv3, cv1, cv2, cv5, 0xffffffffffffffffa0a0a0a0a0a0a0a0] 8 (Tr.N Tr.E [cv34, cv0, cv6, cv3, cv1, cv2, 0xffffffffa0a0a0a0ffffffffa0a0a0a0, cv4] 8 Tr.E)) [cv34, cv0, cv6, cv3, cv1, 0xffffa0a0ffffa0a0ffffa0a0ffffa0a0, cv5, cv4] 8 (Tr.N (Tr.N Tr.E [cv34, cv0, cv6, cv3, 0xffa0ffa0ffa0ffa0ffa0ffa0ffa0ffa0, cv2, cv5, cv4] 8 Tr.E) [cv34, cv0, cv6, cv41, cv1, cv2, cv5, cv4] 8 Tr.E)) [cv34, cv0, cv6, cv1, cv2, cv5, cv4, cv31] 8 (Tr.N (Tr.N (Tr.N Tr.E [cv34, cv0, cv6, cv1, cv2, cv5, cv57] 7 Tr.E) [cv34, cv0, cv47, cv3, cv1, cv2, cv5, cv4] 8 (Tr.N Tr.E [cv34, cv6, cv43, cv1, cv2, cv5, cv4] 7 Tr.E)) [cv34, cv6, cv3, cv41, cv1, cv2, cv5, cv4] 8 (Tr.N (Tr.N Tr.E [cv34, cv6, cv3, cv1, cv2, cv42, cv15] 6 Tr.E) [cv34, cv6, cv3, cv1, cv2, cv5, cv4, cv15] 8 Tr.E))) [cv34, cv6, cv3, cv1, cv2, cv5, 0xffffffffffffffff8888888888888888] 7 (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv34, cv6, cv3, cv1, cv2, cv5, cv15, cv35] 7 Tr.E) [cv34, cv6, cv3, cv1, 0xffff8888ffff8888ffff8888ffff8888, cv5, 0xffffffffffffffff8888888888888888] 6 (Tr.N Tr.E [cv34, cv6, cv3, cv1, 0xffffa0a0ffffa0a0ffffa0a0ffffa0a0, cv5, cv4, cv15] 7 Tr.E)) [cv34, cv6, cv3, cv1, 0xffffa0a0ffffa0a0ffffa0a0ffffa0a0, cv5, 0xffffffffffffffff8888888888888888] 6 (Tr.N (Tr.N Tr.E [cv34, cv6, cv3, cv1, cv5, cv51, cv15] 6 Tr.E) [cv34, cv6, 0xf8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8, cv1, cv2, cv5, cv4] 7 Tr.E)) [0xa0a0a0a0a0a0a0a0aaaaaaaaaaaaaaaa, cv6, cv3, cv1, cv2, cv5, cv4] 7 (Tr.N (Tr.N (Tr.N Tr.E [0xa0a0a0a0a0a0a0a0f0f0f0f0f0f0f0f0, cv0, cv6, cv1, cv2, cv5, cv4] 7 Tr.E) [0xa0a0a0a0a0a0a0a0ffffffffffffffff, cv0, cv6, cv3, cv1, cv2, cv5] 7 Tr.E) [0xa0a0a0a0ffffffffa0a0a0a0ffffffff, cv0, cv6, cv3, cv1, cv2, cv4] 7 (Tr.N (Tr.N Tr.E [0xa0a0ffffa0a0ffffa0a0ffffa0a0ffff, cv0, cv6, cv3, cv1, cv5, cv4] 7 Tr.E) [0xa0ffa0ffa0ffa0ffa0ffa0ffa0ffa0ff, cv0, cv6, cv3, cv2, cv5, cv4] 7 Tr.E))))
def u48 : Tr := Tr.N t46 [cv34, cv0, 0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0, cv6, cv1, cv2, cv5, cv4] 8 t47
def t49 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv48, cv6, cv3, 0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc, cv1, cv2, cv5, cv4] 8 Tr.E) [cv48, cv6, cv3, cv1, cv2, cv42, cv4] 6 (Tr.N Tr.E [cv48, cv6, cv3, cv1, cv2, cv5, cv4] 8 Tr.E)) [cv48, cv6, cv3, cv1, cv2, cv5, cv4, cv35] 7 (Tr.N (Tr.N Tr.E [cv48, cv6, cv3, cv1, cv2, cv5, 0xffffffffffffffffa8a8a8a8a8a8a8a8] 7 Tr.E) [cv48, cv6, cv3, cv1, cv2, 0xffffffffa8a8a8a8ffffffffa8a8a8a8, cv4] 7 Tr.E)) [cv48, cv6, cv3, cv1, 0xffffa8a8ffffa8a8ffffa8a8ffffa8a8, cv5, cv4] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv48, cv6, cv3, cv1, 0xffffa8a8ffffa8a8ffffa8a8ffffa8a8, cv5, 0xffffffffffffffffa8a8a8a8a8a8a8a8] 6 Tr.E) [cv48, cv6, cv3, 0xffa8ffa8ffa8ffa8ffa8ffa8ffa8ffa8, cv2, cv5, cv4] 7 (Tr.N Tr.E [cv48, cv6, 0xf8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8, cv1, cv2, cv5, cv4] 7 Tr.E)) [cv48, cv47, cv3, cv1, cv2, cv5, cv4] 7 (Tr.N (Tr.N Tr.E [0xaa000000aa000000aa000000aa000000, cv0, cv6, cv3, cv1, cv2, cv5, cv4] 8 Tr.E) [0xaa00aa0000000000aa00aa0000000000, cv0, cv6, cv3, cv1, cv2, cv5, cv4] 8 Tr.E))) [0xaa00aa00aa00aa000000000000000000, cv0, cv6, cv3, cv1, cv2, cv5, cv4] 8 (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv37, 0xaaaa0000aaaa0000aaaa0000aaaa0000, cv6, cv3, cv1, cv2, cv5, cv4] 8 Tr.E) [cv37, cv0, cv6, cv3, cv22, cv2, cv5, cv4] 8 (Tr.N Tr.E [cv37, cv0, cv6, cv3, cv1, cv2, cv5, cv4] 9 Tr.E)) [cv37, cv0, cv6, cv3, cv1, cv2, cv5, 0xffffffffffffffffaa00aa00aa00aa00] 8 (Tr.N (Tr.N Tr.E [cv37, cv0, cv6, cv3, cv1, cv2, 0xffffffffaa00aa00ffffffffaa00aa00, cv4] 8 Tr.E) [cv37, cv0, cv6, cv3, cv1, cv55, cv5, cv4] 8 Tr.E)) [cv37, cv0, cv6, cv3, cv58, cv2, cv5, cv4] 8 (Tr.N (Tr.N (Tr.N Tr.E [cv37, cv0, cv6, cv3, cv17, cv5, cv4] 7 Tr.E) [cv37, cv0, cv6, cv3, cv2, cv5, cv27, cv4] 8 Tr.E) [cv37, cv0, cv6, cv3, cv2, cv36, cv4] 7 (Tr.N (Tr.N Tr.E [cv37, cv0, cv6, cv38, cv1, cv2, cv5, cv4] 8 Tr.E) [cv37, cv0, cv29, cv3, cv1, cv2, cv5, cv4] 8 Tr.E))))
def t50 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv37, cv6, cv3, cv1, cv58, cv2, cv5, cv4] 8 Tr.E) [cv37, cv6, cv3, cv1, cv2, cv5, cv13, cv4] 8 (Tr.N Tr.E [cv37, cv6, cv3, cv1, cv2, cv13, cv24, cv4] 7 Tr.E)) [cv37, cv29, cv3, cv1, cv2, cv5, cv13, cv4] 7 (Tr.N (Tr.N Tr.E [cv37, cv3, cv1, cv2, cv12, cv13, cv4] 6 Tr.E) [cv37, cv3, cv1, cv2, cv13, cv11, cv4] 6 Tr.E)) [cv37, cv3, cv52, cv21, cv5, cv4] 5 (Tr.N (Tr.N (Tr.N Tr.E [0xaa00aa00aa00aa00ffffffffffffffff, cv0, cv6, cv3, cv1, cv2, cv5] 7 Tr.E) [0xaa00aa00aaaaaaaaaa00aa00aaaaaaaa, cv6, cv3, cv1, cv2, cv5, cv4] 7 Tr.E) [0xaa00aa00ff00ff00aa00aa00ff00ff00, cv0, cv6, cv3, cv2, cv5, cv4] 7 (Tr.N (Tr.N Tr.E [0xaa00aa00ffffffffaa00aa00ffffffff, cv0, cv6, cv3, cv1, cv2, cv4] 7 Tr.E) [0xaa00ffffaa00ffffaa00ffffaa00ffff, cv0, cv6, cv3, cv1, cv5, cv4] 7 Tr.E))) [0xaa88aa88aa88aa88aa88aa88aa88aa88, cv0, cv6, cv3, cv1, cv2, cv5, cv4] 8 (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [0xaaa0aaa0aaa0aaa0aaa0aaa0aaa0aaa0, cv0, cv6, cv3, cv1, cv2, cv5, cv4] 8 Tr.E) [0xaaa0aaa0aaa0aaa0aaa0aaa0aaa0aaa0, cv6, cv41, cv1, cv2, cv5, cv4] 7 (Tr.N Tr.E [0xaaa8aaa8aaa8aaa8aaa8aaa8aaa8aaa8, cv6, cv3, cv1, cv2, cv5, cv4] 7 Tr.E)) [0xaaaa000000000000aaaa000000000000, cv0, cv6, cv3, cv1, cv2, cv5, cv4] 8 (Tr.N (Tr.N Tr.E [0xaaaa0000aaaa00000000000000000000, cv0, cv6, cv3, cv1, cv2, cv5, cv4] 8 Tr.E) [0xaaaa0000aaaa0000aaaa0000aaaa0000, cv0, cv6, cv3, cv22, cv1, cv5, cv4] 8 Tr.E)) [0xaaaa0000aaaa0000aaaa0000aaaa0000, cv0, cv6, cv3, cv1, cv2, cv5, cv4] 9 (Tr.N (Tr.N (Tr.N Tr.E [0xaaaa0000aaaa0000aaaa0000aaaa0000, cv0, cv6, cv3, cv1, cv2, cv5, 0xffffffffffffffffaaaa0000aaaa0000] 8 Tr.E) [0xaaaa0000aaaa0000aaaa0000aaaa0000, cv0, cv6, cv3, cv1, cv23, cv5, cv4] 8 Tr.E) [0xaaaa0000aaaa0000aaaa0000aaaa0000, cv6, cv3, cv1, cv39, cv5, cv4] 7 (Tr.N (Tr.N Tr.E [0xaaaa0000aaaa0000aaaa0000aaaa0000, cv6, cv3, cv1, cv2, cv23, cv5, cv4] 8 Tr.E) [0xaaaa0000aaaa0000aaaa0000aaaa0000, cv6, cv3, cv1, cv55, cv5, cv4] 7 Tr.E))))
def u51 : Tr := Tr.N t49 [cv37, cv0, cv21, cv32, cv5, cv4] 5 t50
def u52 : Tr := Tr.N u48 [cv48, cv0, cv6, cv3, cv1, cv2, cv5, cv4] 8 u51
def t53 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [0xaaaa8888aaaa8888aaaa8888aaaa8888, cv0, cv6, cv3, cv1, cv2, cv5, cv4] 8 Tr.E) [0xaaaaa0a0aaaaa0a0aaaaa0a0aaaaa0a0, cv0, cv6, cv3, cv1, cv2, cv5, cv4] 8 (Tr.N Tr.E [0xaaaaa8a8aaaaa8a8aaaaa8a8aaaaa8a8, cv6, cv3, cv1, cv2, cv5, cv4] 7 Tr.E)) [0xaaaaaa00aaaaaa00aaaaaa00aaaaaa00, cv0, cv6, cv3, cv1, cv2, cv5, cv4] 8 (Tr.N (Tr.N Tr.E [0xaaaaaa00aaaaaa00aaaaaa00aaaaaa00, cv6, cv3, cv1, cv2, 0xffffff0000000000ffffff0000000000, cv4] 7 Tr.E) [0xaaaaaa00aaaaaa00aaaaaa00aaaaaa00, cv6, cv3, cv1, cv2, 0xffffff00ffffff00ffffff00ffffff00, cv5, cv4] 8 Tr.E)) [0xaaaaaa00aaaaaa00aaaaaa00aaaaaa00, cv6, cv3, cv1, cv2, cv5, cv24, cv4] 7 (Tr.N (Tr.N (Tr.N Tr.E [0xaaaaaa00aaaaaa00aaaaaa00aaaaaa00, cv6, cv3, cv1, cv2, cv5, cv4] 8 Tr.E) [0xaaaaaa00aaaaaa00aaaaaa00aaaaaa00, cv6, cv3, cv1, cv2, cv5, 0xffffffffffffffffaaaaaa00aaaaaa00] 7 (Tr.N Tr.E [0xaaaaaa00aaaaaa00aaaaaa00aaaaaa00, cv6, cv3, cv1, cv55, cv5, cv4] 7 Tr.E)) [0xaaaaaa88aaaaaa88aaaaaa88aaaaaa88, cv6, cv3, cv1, cv2, cv5, cv4] 7 (Tr.N (Tr.N Tr.E [0xaaaaaaa0aaaaaaa0aaaaaaa0aaaaaaa0, cv6, cv3, cv1, cv2, cv5, cv4] 7 Tr.E) [0xaaaaaaaa000000000000000000000000, cv0, cv6, cv3, cv1, cv2, cv5, cv4] 8 Tr.E))) [0xaaaaaaaa00000000aaaaaaaa00000000, cv0, cv6, cv3, cv1, cv2, cv5, cv4] 9 (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [0xaaaaaaaa00000000aaaaaaaa00000000, cv0, cv6, cv3, cv1, cv2, cv13, cv4] 8 Tr.E) [0xaaaaaaaa00000000aaaaaaaa00000000, cv6, cv3, cv1, cv2, cv5, cv13, cv4] 8 (Tr.N Tr.E [0xaaaaaaaa88888888aaaaaaaa88888888, cv0, cv6, cv3, cv1, cv2, cv5, cv4] 8 Tr.E)) [0xaaaaaaaaa0a0a0a0aaaaaaaaa0a0a0a0, cv0, cv6, cv3, cv1, cv2, cv5, cv4] 8 (Tr.N (Tr.N Tr.E [0xaaaaaaaaa8a8a8a8aaaaaaaaa8a8a8a8, cv6, cv3, cv1, cv2, cv5, cv4] 7 Tr.E) [0xaaaaaaaaaa00aa00aaaaaaaaaa00aa00, cv0, cv6, cv3, cv1, cv2, cv5, cv4] 8 Tr.E)) [0xaaaaaaaaaaaa0000aaaaaaaaaaaa0000, cv0, cv6, cv3, cv1, cv2, cv5, cv4] 8 (Tr.N (Tr.N (Tr.N Tr.E [0xaaaaaaaaaaaaa0a0aaaaaaaaaaaaa0a0, cv6, cv3, cv1, cv2, cv5, cv4] 7 Tr.E) [0xaaaaaaaaaaaaaa00aaaaaaaaaaaaaa00, cv6, cv3, cv1, cv2, cv5, cv4] 7 Tr.E) [0xaaaaaaaaaaaaaaaa0000000000000000, cv0, cv6, cv3, cv1, cv2, cv5, cv4] 9 (Tr.N (Tr.N Tr.E [0xaaaaaaaaaaaaaaaa0000000000000000, cv0, cv6, cv3, cv1, cv2, cv5, cv15] 8 Tr.E) [0xaaaaaaaaaaaaaaaa0000000000000000, cv0, cv6, cv3, cv1, 0xffffaaaaffffaaaaffff0000ffff0000, cv5, cv4] 8 Tr.E))))
def t54 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [0xaaaaaaaaaaaaaaaa8888888888888888, cv0, cv6, cv3, cv1, cv2, cv5, cv4] 8 Tr.E) [0xaaaaaaaaaaaaaaaaa0a0a0a0a0a0a0a0, cv0, cv6, cv3, cv1, cv2, cv5, cv4] 8 (Tr.N Tr.E [0xaaaaaaaaaaaaaaaaa8a8a8a8a8a8a8a8, cv6, cv3, cv1, cv2, cv5, cv4] 7 Tr.E)) [0xaaaaaaaaaaaaaaaaaa00aa00aa00aa00, cv0, cv6, cv3, cv1, cv2, cv5, cv4] 8 (Tr.N (Tr.N Tr.E [0xaaaaaaaaaaaaaaaaaa88aa88aa88aa88, cv6, cv3, cv1, cv2, cv5, cv4] 7 Tr.E) [0xaaaaaaaaaaaaaaaaaaaa0000aaaa0000, cv0, cv6, cv3, cv1, cv2, cv5, cv4] 8 Tr.E)) [0xaaaaaaaaaaaaaaaaaaaaaa00aaaaaa00, cv6, cv3, cv1, cv2, cv5, cv4] 7 (Tr.N (Tr.N (Tr.N Tr.E [0xaaaaaaaaaaaaaaaaaaaaaaaa00000000, cv0, cv6, cv3, cv1, cv2, cv5, cv4] 8 Tr.E) [0xaaaaaaaaaaaaaaaaaaaaaaaa88888888, cv6, cv3, cv1, cv2, cv5, cv4] 7 Tr.E) [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaa0000, cv6, cv3, cv1, cv2, cv5, cv4] 7 (Tr.N (Tr.N Tr.E [cv0, cv0, cv6, cv3, cv1, cv2, cv5, cv4] 9 Tr.E) [cv0, 0xaaaaaaaaaaaaaaaaffffffffffffffff, cv6, cv3, cv1, cv2, cv5, cv4] 8 Tr.E))) [cv0, 0xaaaaaaaaffffffffaaaaaaaaffffffff, cv6, cv3, cv1, cv2, cv5, cv4] 8 (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv0, 0xaaaaffffaaaaffff0000ffff0000ffff, cv6, cv3, cv1, cv5, cv4] 7 Tr.E) [cv0, 0xaaaaffffaaaaffffaaaaffffaaaaffff, cv6, cv3, cv1, cv2, cv5, cv4] 8 (Tr.N Tr.E [cv0, 0xaaffaaffaaffaaffaaffaaffaaffaaff, cv6, cv3, cv1, cv2, cv5, cv4] 8 Tr.E)) [cv0, 0xaf0faf0faf0faf0faf0faf0faf0faf0f, cv6, cv1, cv2, cv5, cv4] 7 (Tr.N (Tr.N Tr.E [cv0, 0xafafafafafafafafafafafafafafafaf, cv6, cv3, cv1, cv2, cv5, cv4] 8 Tr.E) [cv0, 0xb3b3b3b3b3b3b3b3b3b3b3b3b3b3b3b3, cv3, cv1, cv2, cv5, cv4] 7 Tr.E)) [cv0, 0xbb33bb33bb33bb33bb33bb33bb33bb33, cv3, cv1, cv2, cv5, cv4] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv0, 0xbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb, cv6, cv3, cv1, cv2, cv5, cv4] 8 Tr.E) [cv0, cv6, 0xe0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0, cv33, cv1, cv2, cv5, cv4] 8 Tr.E) [cv0, cv6, 0xe0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0, cv3, cv1, cv2, cv5, cv4] 8 (Tr.N (Tr.N Tr.E [cv0, cv6, 0xe0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0, cv1, cv2, cv5, cv4] 8 Tr.E) [cv0, cv6, 0xe0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0, cv1, cv2, cv5, 0xffffffffffffffffe0e0e0e0e0e0e0e0] 7 Tr.E))))
def u55 : Tr := Tr.N t53 [0xaaaaaaaaaaaaaaaa0000000000000000, cv6, cv3, cv1, cv2, cv5, cv4, cv15] 8 t54
def t56 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv0, cv6, cv43, cv3, cv1, cv2, cv5, cv4] 8 Tr.E) [cv0, cv6, 0xee00ee00ee00ee00ee00ee00ee00ee00, cv3, cv1, cv2, cv5, cv4] 8 (Tr.N Tr.E [cv0, cv6, 0xeeaaeeaaeeaaeeaaeeaaeeaaeeaaeeaa, cv3, cv1, cv2, cv5, cv4] 8 Tr.E)) [cv0, cv6, cv29, cv3, cv1, cv2, cv5, cv4] 8 (Tr.N (Tr.N Tr.E [cv0, cv6, 0xeeee0000eeee0000eeee0000eeee0000, cv3, cv1, cv2, cv5, cv4] 8 Tr.E) [cv0, cv6, 0xeeeeaaaaeeeeaaaaeeeeaaaaeeeeaaaa, cv3, cv1, cv2, cv5, cv4] 8 Tr.E)) [cv0, cv6, 0xeeeecccceeeecccceeeecccceeeecccc, cv3, cv1, cv2, cv5, cv4] 8 (Tr.N (Tr.N (Tr.N Tr.E [cv0, cv6, cv33, cv3, cv1, cv26, cv2, cv5, cv4] 8 Tr.E) [cv0, cv6, cv33, cv3, cv1, 0xffff0000f0f00000ffff0000f0f00000, cv5, cv4] 7 (Tr.N Tr.E [cv0, cv6, cv33, cv3, cv1, cv17, cv5, cv4] 7 Tr.E)) [cv0, cv6, cv33, cv3, cv1, 0xffff0000ffff0000ffff000000000000, cv5, cv4] 7 (Tr.N (Tr.N Tr.E [cv0, cv6, cv33, cv3, cv1, cv2, cv5, cv27, cv4] 8 Tr.E) [cv0, cv6, cv33, cv3, cv1, cv2, cv5, 0xffffffffffff0000ffffffffffff0000, cv4] 8 Tr.E))) [cv0, cv6, cv33, cv3, cv1, cv2, cv5, cv4] 9 (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv0, cv6, cv33, cv3, cv1, cv2, cv5, cv19] 7 Tr.E) [cv0, cv6, cv33, cv3, cv1, cv2, cv36, cv4] 7 (Tr.N Tr.E [cv0, cv6, cv33, cv1, cv2, cv20, cv5, cv4] 7 Tr.E)) [cv0, cv6, 0xf0000000f0000000f0000000f0000000, cv3, cv1, cv2, cv5, cv4] 8 (Tr.N (Tr.N Tr.E [cv0, cv6, 0xf000f00000000000f000f00000000000, cv3, cv1, cv2, cv5, cv4] 8 Tr.E) [cv0, cv6, 0xf000f000f000f0000000000000000000, cv3, cv1, cv2, cv5, cv4] 8 Tr.E)) [cv0, cv6, 0xf000f000f000f000f000f000f000f000, cv3, cv1, cv2, cv5, cv4] 9 (Tr.N (Tr.N (Tr.N Tr.E [cv0, cv6, 0xf000f000f000f000f000f000f000f000, cv3, cv28, cv2, cv5, cv4] 8 Tr.E) [cv0, cv6, 0xf000f000f000f000f000f000f000f000, cv1, cv28, cv2, cv5, cv4] 8 Tr.E) [cv0, cv6, 0xf0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0, cv3, cv1, cv2, cv5, cv4] 8 (Tr.N (Tr.N Tr.E [cv0, cv6, 0xf0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0, cv3, cv1, cv2, cv5, cv4] 8 Tr.E) [cv0, cv6, 0xf0e0f0e0f0e0f0e0f0e0f0e0f0e0f0e0, cv1, cv2, cv5, cv4] 7 Tr.E))))
def t57 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv0, cv6, cv54, 0xf0f0f0f000000000f0f0f0f000000000, cv1, cv2, cv5, cv4] 8 Tr.E) [cv0, cv6, cv54, cv3, cv1, cv26, cv5, cv4] 8 (Tr.N Tr.E [cv0, cv6, cv54, cv3, cv1, cv2, cv5, cv4] 9 Tr.E)) [cv0, cv6, cv54, cv3, cv1, cv2, cv5, 0xfffffffffffffffff0f00000f0f00000] 8 (Tr.N (Tr.N Tr.E [cv0, cv6, cv54, cv3, cv1, cv50, cv5, cv4] 8 Tr.E) [cv0, cv6, cv54, cv3, cv1, cv5, cv4, cv35] 8 Tr.E)) [cv0, cv6, cv54, cv3, cv1, cv5, cv19] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv0, cv6, cv54, cv1, cv2, cv50, cv5, cv4] 8 Tr.E) [cv0, cv6, cv54, cv1, cv2, cv5, cv4, cv31] 8 Tr.E) [cv0, cv6, 0xf0f00000f0f00000f0f0f0f0f0f0f0f0, cv1, cv2, cv5, cv4] 7 (Tr.N (Tr.N Tr.E [cv0, cv6, 0xf0f00000f0f00000ffff0000ffff0000, cv3, cv1, cv5, cv4] 7 Tr.E) [cv0, cv6, 0xf0f00000f0f00000ffffffffffffffff, cv3, cv1, cv2, cv5] 7 Tr.E))) [cv0, cv6, 0xf0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a0, cv3, cv1, cv2, cv5, cv4] 8 (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv0, cv6, 0xf0f0c0c0f0f0c0c0f0f0c0c0f0f0c0c0, cv3, cv1, cv2, cv5, cv4] 8 Tr.E) [cv0, cv6, 0xf0f0e0e0f0f0e0e0f0f0e0e0f0f0e0e0, cv1, cv2, cv5, cv4] 7 (Tr.N Tr.E [cv0, cv6, 0xf0f0f000f0f0f000f0f0f000f0f0f000, cv3, cv1, cv2, cv5, cv4] 8 Tr.E)) [cv0, cv6, 0xf0f0f0a0f0f0f0a0f0f0f0a0f0f0f0a0, cv1, cv2, cv5, cv4] 7 (Tr.N (Tr.N Tr.E [cv0, cv6, 0xf0f0f0f0f000f000f0f0f0f0f000f000, cv3, cv1, cv2, cv5, cv4] 8 Tr.E) [cv0, cv6, 0xf0f0f0f0f0f00000f0f0f0f0f0f00000, cv3, cv1, cv2, cv5, cv4] 8 Tr.E)) [cv0, cv6, 0xf0f0f0f0f0f00000f0f0f0f0f0f00000, 0xff00ff00ff000000ff00ff00ff000000, cv2, cv5, cv4] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv0, cv6, 0xf0f0f0f0f0f00000f0f0f0f0f0f00000, cv1, cv2, cv5, 0xffffffffffff0000ffffffffffff0000, cv4] 8 Tr.E) [cv0, cv6, 0xf0f0f0f0f0f00000f0f0f0f0f0f00000, cv1, cv2, cv5, cv4] 8 Tr.E) [cv0, cv6, 0xf0f0f0f0f0f0a0a0f0f0f0f0f0f0a0a0, cv1, cv2, cv5, cv4] 7 (Tr.N (Tr.N Tr.E [cv0, cv6, 0xf0f0f0f0f0f0f000f0f0f0f0f0f0f000, cv1, cv2, cv5, cv4] 7 Tr.E) [cv0, cv6, 0xf0f0f0f0f0f0f0f0f000f000f000f000, cv3, cv1, cv2, cv5, cv4] 8 Tr.E))))
def u58 : Tr := Tr.N t56 [cv0, cv6, 0xf0f0000000000000f0f0000000000000, cv3, cv1, cv2, cv5, cv4] 8 t57
def u59 : Tr := Tr.N u55 [cv0, cv6, 0xe0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0, cv1, cv2, 0xffffffffe0e0e0e0ffffffffe0e0e0e0, cv4] 7 u58
def u60 : Tr := Tr.N u52 [0xaaaa0000aaaa0000ffffffffffffffff, cv0, cv6, cv3, cv1, cv2, cv5] 7 u59
def u61 : Tr := Tr.N u45 [0x37373737373737373737373737373737, cv0, cv3, cv1, cv2, cv5, cv4] 7 u60
def u62 : Tr := Tr.N u30 [cv10, cv0, cv6, 0xff000f00ff000f00ff000f00ff000f00, cv2, cv5, cv4] 7 u61
def t63 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv0, cv6, cv3, 0xf0f0f0f0f0f0f0f0ffffffffffffffff, cv1, cv2, cv5, cv4] 8 Tr.E) [cv0, cv6, cv3, 0xf0f0f0f0fffffffff0f0f0f0ffffffff, cv1, cv2, cv5, cv4] 8 (Tr.N Tr.E [cv0, cv6, cv3, 0xf3f3f3f3f3f3f3f3f3f3f3f3f3f3f3f3, cv1, cv2, cv5, cv4] 8 Tr.E)) [cv0, cv6, cv3, 0xf8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8, cv1, cv2, cv5, cv4] 8 (Tr.N (Tr.N Tr.E [cv0, cv6, cv3, 0xfa00fa00fa00fa00fa00fa00fa00fa00, cv1, cv2, cv5, cv4] 8 Tr.E) [cv0, cv6, cv3, 0xfaaafaaafaaafaaafaaafaaafaaafaaa, cv1, cv2, cv5, cv4] 8 Tr.E)) [cv0, cv6, cv3, cv38, cv1, cv2, cv5, cv4] 8 (Tr.N (Tr.N (Tr.N Tr.E [cv0, cv6, cv3, 0xfafa0000fafa0000fafa0000fafa0000, cv1, cv2, cv5, cv4] 8 Tr.E) [cv0, cv6, cv3, 0xfafaaaaafafaaaaafafaaaaafafaaaaa, cv1, cv2, cv5, cv4] 8 (Tr.N Tr.E [cv0, cv6, cv3, 0xfafaf0f0fafaf0f0fafaf0f0fafaf0f0, cv1, cv2, cv5, cv4] 8 Tr.E)) [cv0, cv6, cv3, 0xfafafafa00000000fafafafa00000000, cv1, cv2, cv5, cv4] 8 (Tr.N (Tr.N Tr.E [cv0, cv6, cv3, 0xfafafafaaaaaaaaafafafafaaaaaaaaa, cv1, cv2, cv5, cv4] 8 Tr.E) [cv0, cv6, cv3, 0xfafafafaf0f0f0f0fafafafaf0f0f0f0, cv1, cv2, cv5, cv4] 8 Tr.E))) [cv0, cv6, cv3, 0xfafafafafafafafa0000000000000000, cv1, cv2, cv5, cv4] 8 (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv0, cv6, cv3, 0xfafafafafafafafaaaaaaaaaaaaaaaaa, cv1, cv2, cv5, cv4] 8 Tr.E) [cv0, cv6, cv3, 0xfafafafafafafafaf0f0f0f0f0f0f0f0, cv1, cv2, cv5, cv4] 8 (Tr.N Tr.E [cv0, cv6, cv3, cv41, cv1, cv2, cv42, cv4] 7 Tr.E)) [cv0, cv6, cv3, cv41, cv1, cv2, cv5, cv4] 9 (Tr.N (Tr.N Tr.E [cv0, cv6, cv3, cv41, cv1, cv2, cv5, cv4, cv35] 8 Tr.E) [cv0, cv6, cv3, cv41, cv1, cv2, cv5, cv19] 7 Tr.E)) [cv0, cv6, cv3, cv41, cv1, cv5, cv51, cv4] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv0, cv6, cv3, 0xfe00fe00fe00fe00fe00fe00fe00fe00, cv2, cv5, cv4] 7 Tr.E) [cv0, cv6, cv3, 0xfefe0000fefe0000fefe0000fefe0000, cv1, cv5, cv4] 7 Tr.E) [cv0, cv6, cv3, 0xfefefefefefefefefefefefefefefefe, cv1, cv2, cv5, cv4] 8 (Tr.N (Tr.N Tr.E [cv0, cv6, cv3, 0xff00000000000000ff00000000000000, cv1, cv2, cv5, cv4] 8 Tr.E) [cv0, cv6, cv3, 0xff000000ff0000000000000000000000, cv1, cv2, cv5, cv4] 8 Tr.E))))
def t64 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv0, cv6, cv3, cv22, cv1, cv26, cv5, cv4] 8 Tr.E) [cv0, cv6, cv3, cv22, cv1, cv2, cv5, cv4] 9 (Tr.N Tr.E [cv0, cv6, cv3, cv22, cv1, cv2, cv5, cv53] 8 Tr.E)) [cv0, cv6, cv3, cv22, cv1, cv2, cv36, cv4] 8 (Tr.N (Tr.N Tr.E [cv0, cv6, cv3, cv22, cv1, cv25, cv5, cv4] 8 Tr.E) [cv0, cv6, cv3, cv22, cv1, cv50, cv5, cv4] 8 Tr.E)) [cv0, cv6, cv3, cv22, cv1, 0xffffff00ffffff00ffffff00ffffff00, cv5, cv4] 8 (Tr.N (Tr.N (Tr.N Tr.E [cv0, cv6, cv3, cv22, cv1, cv42, cv4] 7 Tr.E) [cv0, cv6, cv3, cv22, cv1, cv5, cv4, cv35] 8 (Tr.N Tr.E [cv0, cv6, cv3, cv22, cv1, cv5, 0xffffffffffffffffaaaa0000aaaa0000] 7 Tr.E)) [cv0, cv6, cv3, cv22, cv1, cv5, cv19] 7 (Tr.N (Tr.N Tr.E [cv0, cv6, cv3, cv22, cv16, cv2, cv5, cv4] 8 Tr.E) [cv0, cv6, cv3, cv22, cv28, cv2, cv5, cv4] 8 Tr.E))) [cv0, cv6, cv3, cv22, cv2, 0xffffff00ffffff00ffffff00ffffff00, cv5, cv4] 8 (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv0, cv6, cv3, cv22, cv2, cv5, cv4, cv45] 8 Tr.E) [cv0, cv6, cv3, cv22, cv2, cv5, 0xffffffffffffffffaa00aa00aa00aa00] 7 (Tr.N Tr.E [cv0, cv6, cv3, 0xff000000ff000000ff00ff00ff00ff00, cv2, cv5, cv4] 7 Tr.E)) [cv0, cv6, cv3, 0xff000000ff000000ffff0000ffff0000, cv1, cv5, cv4] 7 (Tr.N (Tr.N Tr.E [cv0, cv6, cv3, 0xff000000ff000000ffffffffffffffff, cv1, cv2, cv5] 7 Tr.E) [cv0, cv6, cv3, 0xff000000ffffffffff000000ffffffff, cv1, cv2, cv4] 7 Tr.E)) [cv0, cv6, cv3, 0xff000f00ff000f00ff000f00ff000f00, cv2, cv5, cv4] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv0, cv6, cv3, 0xff003300ff003300ff003300ff003300, cv2, cv5, cv4] 7 Tr.E) [cv0, cv6, cv3, 0xff00aa00ff000000ff00aa00ff000000, cv2, cv5, cv4] 7 Tr.E) [cv0, cv6, cv3, cv40, cv1, cv2, cv5, cv4] 8 (Tr.N (Tr.N Tr.E [cv0, cv6, cv3, cv40, cv26, cv5, cv4] 7 Tr.E) [cv0, cv6, cv3, cv40, cv2, cv23, cv5, cv4] 8 Tr.E))))
def u65 : Tr := Tr.N t63 [cv0, cv6, cv3, cv22, 0xff00ff0000000000ff00ff0000000000, cv2, cv5, cv4] 8 t64
def t66 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv0, cv6, cv3, cv40, cv2, cv5, 0xffffffffffffffffff00aa00ff00aa00] 7 Tr.E) [cv0, cv6, cv3, cv40, cv2, 0xffffffffff00aa00ffffffffff00aa00, cv4] 7 (Tr.N Tr.E [cv0, cv6, cv3, cv40, cv55, cv5, cv4] 7 Tr.E)) [cv0, cv6, cv3, cv40, cv42, cv4] 6 (Tr.N (Tr.N Tr.E [cv0, cv6, cv3, cv40, cv5, cv4, cv35] 7 Tr.E) [cv0, cv6, cv3, cv40, cv5, cv19] 6 Tr.E)) [cv0, cv6, cv3, 0xff00cc00ff00cc00ff00cc00ff00cc00, cv1, cv2, cv5, cv4] 8 (Tr.N (Tr.N (Tr.N Tr.E [cv0, cv6, cv3, 0xff00ee00ff00ee00ff00ee00ff00ee00, cv2, cv5, cv4] 7 Tr.E) [cv0, cv6, cv3, 0xff00f000ff00f000ff00f000ff00f000, cv1, cv2, cv5, cv4] 8 (Tr.N Tr.E [cv0, cv6, cv3, 0xff00fa00ff00fa00ff00fa00ff00fa00, cv2, cv5, cv4] 7 Tr.E)) [cv0, cv6, cv3, 0xff00ff0000000000ff00ff0000000000, cv1, cv26, cv2, cv4] 8 (Tr.N (Tr.N Tr.E [cv0, cv6, cv3, 0xff00ff0000000000ff00ff0000000000, cv1, cv2, cv5, cv4] 9 Tr.E) [cv0, cv6, cv3, 0xff00ff0000000000ff00ff0000000000, cv1, cv2, cv27, cv4] 8 Tr.E))) [cv0, cv6, cv3, 0xff00ff0000000000ff00ff0000000000, cv2, cv56, cv4] 7 (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv0, cv6, cv3, 0xff00ff0000000000ff00ff0000000000, cv2, cv5, cv27, cv4] 8 Tr.E) [cv0, cv6, cv3, 0xff00ff0000000000ff00ff0000000000, cv2, cv36, cv4] 7 (Tr.N Tr.E [cv0, cv6, cv3, 0xff00ff00aa00aa00ff00ff00aa00aa00, cv1, cv2, cv5, cv4] 8 Tr.E)) [cv0, cv6, cv3, 0xff00ff00cc00cc00ff00ff00cc00cc00, cv1, cv2, cv5, cv4] 8 (Tr.N (Tr.N Tr.E [cv0, cv6, cv3, 0xff00ff00f000f000ff00ff00f000f000, cv1, cv2, cv5, cv4] 8 Tr.E) [cv0, cv6, cv3, 0xff00ff00ff000000ff00ff00ff000000, cv1, cv2, cv5, cv4] 8 Tr.E)) [cv0, cv6, cv3, 0xff00ff00ff000000ff00ff00ff000000, cv2, cv5, 0xffffffffffff00000000000000000000] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv0, cv6, cv3, 0xff00ff00ff000000ff00ff00ff000000, cv2, cv5, 0xffffffffffff0000ffffffffffff0000, cv4] 8 Tr.E) [cv0, cv6, cv3, 0xff00ff00ff000000ff00ff00ff000000, cv2, cv5, cv4] 8 Tr.E) [cv0, cv6, cv3, 0xff00ff00ff000000ff00ff00ff000000, cv2, cv36, cv4] 7 (Tr.N (Tr.N Tr.E [cv0, cv6, cv3, 0xff00ff00ff00aa00ff00ff00ff00aa00, cv2, cv5, cv4] 7 Tr.E) [cv0, cv6, cv3, 0xff00ff00ff00cc00ff00ff00ff00cc00, cv2, cv5, cv4] 7 Tr.E))))
def t67 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv0, cv6, cv3, 0xff00ff00ff00ff000000000000000000, cv1, cv2, cv5, cv4] 9 Tr.E) [cv0, cv6, cv3, 0xff00ff00ff00ff000000000000000000, cv1, cv2, cv5, cv31] 8 (Tr.N Tr.E [cv0, cv6, cv3, 0xff00ff00ff00ff000000000000000000, cv1, cv2, cv5, cv45] 8 Tr.E)) [cv0, cv6, cv3, 0xff00ff00ff00ff000f000f000f000f00, cv2, cv5, cv4] 7 (Tr.N (Tr.N Tr.E [cv0, cv6, cv3, 0xff00ff00ff00ff00aa00aa00aa00aa00, cv1, cv2, cv5, cv4] 8 Tr.E) [cv0, cv6, cv3, 0xff00ff00ff00ff00cc00cc00cc00cc00, cv1, cv2, cv5, cv4] 8 Tr.E)) [cv0, cv6, cv3, 0xff00ff00ff00ff00ee00ee00ee00ee00, cv2, cv5, cv4] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv0, cv6, cv3, 0xff00ff00ff00ff00f000f000f000f000, cv1, cv2, cv5, cv4] 8 Tr.E) [cv0, cv6, cv3, 0xff00ff00ff00ff00ff000000ff000000, cv1, cv2, cv5, cv4] 8 Tr.E) [cv0, cv6, cv3, 0xff00ff00ff00ff00ff00aa00ff00aa00, cv2, cv5, cv4] 7 (Tr.N (Tr.N Tr.E [cv0, cv6, cv3, 0xff00ff00ff00ff00ff00ff0000000000, cv1, cv2, cv5, cv4] 8 Tr.E) [cv0, cv6, cv3, 0xff00ff00ff00ff00ff00ff00cc00cc00, cv2, cv5, cv4] 7 Tr.E))) [cv0, cv6, cv3, 0xff00ff00ff00ff00ff00ff00ff000000, cv2, cv5, cv4] 7 (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv0, cv6, cv3, cv1, cv1, cv2, cv5, cv4] 9 Tr.E) [cv0, cv6, cv3, cv1, 0xff00ff00ff00ff00ffffffffffffffff, cv2, cv5, cv4] 8 (Tr.N Tr.E [cv0, cv6, cv3, cv1, 0xff00ff00ffffffffff00ff00ffffffff, cv2, cv5, cv4] 8 Tr.E)) [cv0, cv6, cv3, cv1, 0xff00ffffff00ffffff00ffffff00ffff, cv2, cv5, cv4] 8 (Tr.N (Tr.N Tr.E [cv0, cv6, cv3, cv1, 0xff0f0000ff0f0000ff0f0000ff0f0000, cv5, cv4] 7 Tr.E) [cv0, cv6, cv3, cv1, 0xff0fff0fff0fff0fff0fff0fff0fff0f, cv2, cv5, cv4] 8 Tr.E)) [cv0, cv6, cv3, cv1, 0xff330000ff330000ff330000ff330000, cv5, cv4] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv0, cv6, cv3, cv1, 0xff33ff33ff33ff33ff33ff33ff33ff33, cv2, cv5, cv4] 8 Tr.E) [cv0, cv6, cv3, cv1, 0xff55ff55ff55ff55ff55ff55ff55ff55, cv2, cv5, cv4] 8 Tr.E) [cv0, cv6, cv3, cv1, 0xff88ff88ff88ff88ff88ff88ff88ff88, cv2, cv5, cv4] 8 (Tr.N (Tr.N Tr.E [cv0, cv6, cv3, cv1, 0xffa0ffa0ffa0ffa0ffa0ffa0ffa0ffa0, cv2, cv5, cv4] 8 Tr.E) [cv0, cv6, cv3, cv1, 0xffaa0000ff000000ffaa0000ff000000, cv5, cv4] 7 Tr.E))))
def u68 : Tr := Tr.N t66 [cv0, cv6, cv3, 0xff00ff00ff00f000ff00ff00ff00f000, cv2, cv5, cv4] 7 t67
def u69 : Tr := Tr.N u65 [cv0, cv6, cv3, cv40, cv2, cv5, cv4] 8 u68
def t70 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv0, cv6, cv3, cv1, 0xffaa0000ffaa0000ffaa0000ffaa0000, cv2, cv5, cv4] 8 Tr.E) [cv0, cv6, cv3, cv1, 0xffaa0000ffaa0000ffaa0000ffaa0000, cv5, cv4] 8 (Tr.N Tr.E [cv0, cv6, cv3, cv1, 0xffaa0000ffaa0000ffaa0000ffaa0000, cv5, 0xffffffffffffffffffaa0000ffaa0000] 7 Tr.E)) [cv0, cv6, cv3, cv1, cv39, cv2, cv5, cv4] 8 (Tr.N (Tr.N Tr.E [cv0, cv6, cv3, cv1, 0xffaaff00ffaaff00ffaaff00ffaaff00, cv2, cv5, cv4] 8 Tr.E) [cv0, cv6, cv3, cv1, 0xffaaffaa00000000ffaaffaa00000000, cv2, cv5, cv4] 8 Tr.E)) [cv0, cv6, cv3, cv1, 0xffaaffaaaaaaaaaaffaaffaaaaaaaaaa, cv2, cv5, cv4] 8 (Tr.N (Tr.N (Tr.N Tr.E [cv0, cv6, cv3, cv1, 0xffaaffaaff00ff00ffaaffaaff00ff00, cv2, cv5, cv4] 8 Tr.E) [cv0, cv6, cv3, cv1, 0xffaaffaaffaaffaaaaaaaaaaaaaaaaaa, cv2, cv5, cv4] 8 (Tr.N Tr.E [cv0, cv6, cv3, cv1, 0xffaaffaaffaaffaaff00ff00ff00ff00, cv2, cv5, cv4] 8 Tr.E)) [cv0, cv6, cv3, cv1, cv58, cv2, cv5, cv24, cv4] 8 (Tr.N (Tr.N Tr.E [cv0, cv6, cv3, cv1, cv58, cv2, cv5, cv4] 9 Tr.E) [cv0, cv6, cv3, cv1, 0xffc0ffc0ffc0ffc0ffc0ffc0ffc0ffc0, cv2, cv5, cv4] 8 Tr.E))) [cv0, cv6, cv3, cv1, 0xffcc0000ffcc0000ffcc0000ffcc0000, cv2, cv5, cv4] 8 (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv0, cv6, cv3, cv1, cv14, cv2, cv5, cv4] 8 Tr.E) [cv0, cv6, cv3, cv1, 0xffccff00ffccff00ffccff00ffccff00, cv2, cv5, cv4] 8 (Tr.N Tr.E [cv0, cv6, cv3, cv1, 0xffccffcc00000000ffccffcc00000000, cv2, cv5, cv4] 8 Tr.E)) [cv0, cv6, cv3, cv1, 0xffccffccaa88aa88ffccffccaa88aa88, cv2, cv5, cv4] 7 (Tr.N (Tr.N Tr.E [cv0, cv6, cv3, cv1, 0xffccffccccccccccffccffcccccccccc, cv2, cv5, cv4] 8 Tr.E) [cv0, cv6, cv3, cv1, 0xffccffccff00ff00ffccffccff00ff00, cv2, cv5, cv4] 8 Tr.E)) [cv0, cv6, cv3, cv1, 0xffccffccffccffccff00ff00ff00ff00, cv2, cv5, cv4] 8 (Tr.N (Tr.N (Tr.N Tr.E [cv0, cv6, cv3, cv1, cv16, cv2, cv5, cv13, cv4] 8 Tr.E) [cv0, cv6, cv3, cv1, cv16, cv2, cv5, 0xfffffffff0f0f0f0fffffffff0f0f0f0, cv4] 8 Tr.E) [cv0, cv6, cv3, cv1, cv16, cv2, cv5, cv4] 9 (Tr.N (Tr.N Tr.E [cv0, cv6, cv3, cv1, cv16, cv2, cv59, cv4] 7 Tr.E) [cv0, cv6, cv3, cv1, cv16, cv2, 0xffffffffa0a0a0a0ffffffffa0a0a0a0, cv4] 7 Tr.E))))
def t71 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv0, cv6, cv3, cv1, 0xffee0000ffee0000ffee0000ffee0000, cv5, cv4] 7 Tr.E) [cv0, cv6, cv3, cv1, 0xffeeffeeffeeffeeffeeffeeffeeffee, cv2, cv5, cv4] 8 (Tr.N Tr.E [cv0, cv6, cv3, cv1, 0xfff00000fff00000fff00000fff00000, cv2, cv5, cv4] 8 Tr.E)) [cv0, cv6, cv3, cv1, cv46, cv2, cv5, cv4] 8 (Tr.N (Tr.N Tr.E [cv0, cv6, cv3, cv1, 0xfff0ff00fff0ff00fff0ff00fff0ff00, cv2, cv5, cv4] 8 Tr.E) [cv0, cv6, cv3, cv1, 0xfff0fff000000000fff0fff000000000, cv2, cv5, cv4] 8 Tr.E)) [cv0, cv6, cv3, cv1, 0xfff0fff0f0f0f0f0fff0fff0f0f0f0f0, cv2, cv5, cv4] 8 (Tr.N (Tr.N (Tr.N Tr.E [cv0, cv6, cv3, cv1, 0xfff0fff0ff00ff00fff0fff0ff00ff00, cv2, cv5, cv4] 8 Tr.E) [cv0, cv6, cv3, cv1, 0xfff0fff0fff0fff0f0f0f0f0f0f0f0f0, cv2, cv5, cv4] 8 (Tr.N Tr.E [cv0, cv6, cv3, cv1, 0xfff0fff0fff0fff0ff00ff00ff00ff00, cv2, cv5, cv4] 8 Tr.E)) [cv0, cv6, cv3, cv1, cv28, cv2, cv5, cv24, cv4] 8 (Tr.N (Tr.N Tr.E [cv0, cv6, cv3, cv1, cv28, cv2, cv5, cv4] 9 Tr.E) [cv0, cv6, cv3, cv1, 0xfffa0000fffa0000fffa0000fffa0000, cv5, cv4] 7 Tr.E))) [cv0, cv6, cv3, cv1, 0xfffafffafffafffafffafffafffafffa, cv2, cv5, cv4] 8 (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv0, cv6, cv3, cv1, 0xfffcfffcfffcfffcfffcfffcfffcfffc, cv2, cv5, cv4] 8 Tr.E) [cv0, cv6, cv3, cv1, cv26, cv2, cv5, cv4] 9 (Tr.N Tr.E [cv0, cv6, cv3, cv1, cv26, cv2, cv5, cv19] 8 Tr.E)) [cv0, cv6, cv3, cv1, cv26, cv2, cv13, cv4] 8 (Tr.N (Tr.N Tr.E [cv0, cv6, cv3, cv1, cv26, cv2, cv24, cv4] 8 Tr.E) [cv0, cv6, cv3, cv1, cv26, cv2, 0xffffffffeeeeeeeeffffffffeeeeeeee, cv4] 7 Tr.E)) [cv0, cv6, cv3, cv1, cv26, cv2, 0xffffffffffff0000ffffffffffff0000, cv4] 8 (Tr.N (Tr.N (Tr.N Tr.E [cv0, cv6, cv3, cv1, cv26, cv23, cv24, cv4] 7 Tr.E) [cv0, cv6, cv3, cv1, cv26, cv25, cv13, cv4] 7 Tr.E) [cv0, cv6, cv3, cv1, 0xffff000000000000ffffffffffffffff, cv2, cv5] 7 (Tr.N (Tr.N Tr.E [cv0, cv6, cv3, cv1, 0xffff000033330000ffff000033330000, cv5, cv4] 7 Tr.E) [cv0, cv6, cv3, cv1, 0xffff000055550000ffff000055550000, cv5, cv4] 7 Tr.E))))
def u72 : Tr := Tr.N t70 [cv0, cv6, cv3, cv1, cv16, cv2, 0xffffffffc0c0c0c0ffffffffc0c0c0c0, cv4] 7 t71
def t73 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv0, cv6, cv3, cv1, 0xffff0000cccc0000ffff0000cccc0000, cv2, cv5, cv4] 8 Tr.E) [cv0, cv6, cv3, cv1, 0xffff0000f0000000ffff0000f0000000, cv5, cv4] 7 (Tr.N Tr.E [cv0, cv6, cv3, cv1, 0xffff0000f0f00000ffff000000000000, cv5, cv4] 7 Tr.E)) [cv0, cv6, cv3, cv1, 0xffff0000f0f00000ffff0000f0f00000, cv2, cv5, cv4] 8 (Tr.N (Tr.N Tr.E [cv0, cv6, cv3, cv1, 0xffff0000f0f00000ffff0000f0f00000, cv5, 0xfffffffff0f0f0f0fffffffff0f0f0f0, cv4] 8 Tr.E) [cv0, cv6, cv3, cv1, 0xffff0000f0f00000ffff0000f0f00000, cv5, cv4] 8 Tr.E)) [cv0, cv6, cv3, cv1, 0xffff0000f0f00000ffff0000f0f00000, cv5, 0xffffffffffffffffffff0000f0f00000] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv0, cv6, cv3, cv1, 0xffff0000fafa0000ffff0000fafa0000, cv5, cv4] 7 Tr.E) [cv0, cv6, cv3, cv1, 0xffff0000fcfc0000ffff0000fcfc0000, cv5, cv4] 7 (Tr.N Tr.E [cv0, cv6, cv3, cv1, 0xffff0000ff000000ffff000000000000, cv5, cv4] 7 Tr.E)) [cv0, cv6, cv3, cv1, cv17, cv2, cv5, cv4] 8 (Tr.N (Tr.N Tr.E [cv0, cv6, cv3, cv1, cv17, cv5, cv27, cv4] 8 Tr.E) [cv0, cv6, cv3, cv1, cv17, cv5, cv4] 8 Tr.E))) [cv0, cv6, cv3, cv1, cv17, cv5, 0xffffffffffffffffffff0000ff000000] 7 (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv0, cv6, cv3, cv1, cv17, cv24, cv4] 7 Tr.E) [cv0, cv6, cv3, cv1, cv17, cv36, cv4] 7 (Tr.N Tr.E [cv0, cv6, cv3, cv1, 0xffff0000ffaa0000ffff0000ffaa0000, cv5, cv4] 7 Tr.E)) [cv0, cv6, cv3, cv1, 0xffff0000ffcc0000ffff0000ffcc0000, cv5, cv4] 7 (Tr.N (Tr.N Tr.E [cv0, cv6, cv3, cv1, 0xffff0000fff00000ffff0000fff00000, cv5, cv4] 7 Tr.E) [cv0, cv6, cv3, cv1, 0xffff0000ffff0000ff000000ff000000, cv2, cv5, cv4] 8 Tr.E)) [cv0, cv6, cv3, cv1, 0xffff0000ffff0000ffaa0000ffaa0000, cv5, cv4] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv0, cv6, cv3, cv1, 0xffff0000ffff0000ffff000000000000, cv2, cv5, cv4] 8 Tr.E) [cv0, cv6, cv3, cv1, 0xffff0000ffff0000ffff000000000000, cv5, cv4] 8 Tr.E) [cv0, cv6, cv3, cv1, 0xffff0000ffff0000ffff000000000000, cv5, cv4, 0xffffffffffffffffffffffff00000000] 8 (Tr.N (Tr.N Tr.E [cv0, cv6, cv3, cv1, 0xffff0000ffff0000ffff000000000000, cv5, cv19] 7 Tr.E) [cv0, cv6, cv3, cv1, 0xffff0000ffff0000ffff0000aaaa0000, cv5, cv4] 7 Tr.E))))
def t74 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv0, cv6, cv3, cv1, 0xffff0000ffff0000ffff0000f0f00000, cv5, cv4] 7 Tr.E) [cv0, cv6, cv3, cv1, 0xffff0000ffff0000ffff0000ff000000, cv5, cv4] 7 (Tr.N Tr.E [cv0, cv6, cv3, cv1, cv2, cv2, cv5, cv4] 9 Tr.E)) [cv0, cv6, cv3, cv1, cv2, 0xffff0000ffff0000ffffffffffffffff, cv5, cv4] 8 (Tr.N (Tr.N Tr.E [cv0, cv6, cv3, cv1, cv2, 0xffff0000ffffffffffff0000ffffffff, cv5, cv4] 8 Tr.E) [cv0, cv6, cv3, cv1, cv2, 0xffff00ffffff00ffffff00ffffff00ff, cv5, cv4] 8 Tr.E)) [cv0, cv6, cv3, cv1, cv2, 0xffff0f0fffff0f0fffff0f0fffff0f0f, cv5, cv4] 8 (Tr.N (Tr.N (Tr.N Tr.E [cv0, cv6, cv3, cv1, cv2, 0xffff3333ffff3333ffff3333ffff3333, cv5, cv4] 8 Tr.E) [cv0, cv6, cv3, cv1, cv2, 0xffff5555ffff5555ffff5555ffff5555, cv5, cv4] 8 Tr.E) [cv0, cv6, cv3, cv1, cv2, 0xffff8888ffff8888ffff8888ffff8888, cv5, cv4] 8 (Tr.N (Tr.N Tr.E [cv0, cv6, cv3, cv1, cv2, 0xffffa0a0ffffa0a0ffffa0a0ffffa0a0, cv5, cv4] 8 Tr.E) [cv0, cv6, cv3, cv1, cv2, cv55, cv5, cv4] 8 Tr.E))) [cv0, cv6, cv3, cv1, cv2, cv30, cv5, cv4] 8 (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv0, cv6, cv3, cv1, cv2, 0xffffaaaaffff0000ffffaaaaffff0000, cv5, cv4] 8 Tr.E) [cv0, cv6, cv3, cv1, cv2, 0xffffaaaaffffaaaaffff0000ffff0000, cv5, cv4] 8 (Tr.N Tr.E [cv0, cv6, cv3, cv1, cv2, cv23, cv5, cv24, cv4] 8 Tr.E)) [cv0, cv6, cv3, cv1, cv2, cv23, cv5, cv4] 9 (Tr.N (Tr.N Tr.E [cv0, cv6, cv3, cv1, cv2, cv23, cv5, cv57] 7 Tr.E) [cv0, cv6, cv3, cv1, cv2, 0xffffc0c0ffffc0c0ffffc0c0ffffc0c0, cv5, cv4] 8 Tr.E)) [cv0, cv6, cv3, cv1, cv2, 0xffffcc00ffffcc00ffffcc00ffffcc00, cv5, cv4] 8 (Tr.N (Tr.N (Tr.N Tr.E [cv0, cv6, cv3, cv1, cv2, 0xffffccccaaaa8888ffffccccaaaa8888, cv5, cv4] 7 Tr.E) [cv0, cv6, cv3, cv1, cv2, cv12, cv13, cv4] 7 Tr.E) [cv0, cv6, cv3, cv1, cv2, 0xffffccccffff0000ffffccccffff0000, cv5, cv4] 8 (Tr.N (Tr.N Tr.E [cv0, cv6, cv3, cv1, cv2, 0xffffccccffffccccffff0000ffff0000, cv5, cv4] 8 Tr.E) [cv0, cv6, cv3, cv1, cv2, cv25, cv5, cv13, cv4] 8 Tr.E))))
def u75 : Tr := Tr.N t73 [cv0, cv6, cv3, cv1, 0xffff0000ffff0000ffff0000cccc0000, cv5, cv4] 7 t74
def u76 : Tr := Tr.N u72 [cv0, cv6, cv3, cv1, 0xffff0000aaaa0000ffff0000aaaa0000, cv2, cv5, cv4] 8 u75
def u77 : Tr := Tr.N u69 [cv0, cv6, cv3, cv1, 0xffaa0000ffaa0000ffaa0000ffaa0000, cv58, cv5, cv4] 8 u76
def t78 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv0, cv6, cv3, cv1, cv2, 0xffffeeeeffffeeeeffffeeeeffffeeee, cv5, cv4] 8 Tr.E) [cv0, cv6, cv3, cv1, cv2, 0xfffff000fffff000fffff000fffff000, cv5, cv4] 8 (Tr.N Tr.E [cv0, cv6, cv3, cv1, cv2, cv20, cv5, cv4] 8 Tr.E)) [cv0, cv6, cv3, cv1, cv2, 0xfffff0f0ffff0000fffff0f0ffff0000, cv5, cv4] 8 (Tr.N (Tr.N Tr.E [cv0, cv6, cv3, cv1, cv2, 0xfffff0f0fffff0f0ffff0000ffff0000, cv5, cv4] 8 Tr.E) [cv0, cv6, cv3, cv1, cv2, cv50, cv5, cv4] 9 Tr.E)) [cv0, cv6, cv3, cv1, cv2, 0xfffffafafffffafafffffafafffffafa, cv5, cv4] 8 (Tr.N (Tr.N (Tr.N Tr.E [cv0, cv6, cv3, cv1, cv2, 0xfffffcfcfffffcfcfffffcfcfffffcfc, cv5, cv4] 8 Tr.E) [cv0, cv6, cv3, cv1, cv2, cv56, cv5, cv4] 8 (Tr.N Tr.E [cv0, cv6, cv3, cv1, cv2, 0xffffff00ffff0000ffffff00ffff0000, cv5, cv4] 8 Tr.E)) [cv0, cv6, cv3, cv1, cv2, 0xffffff00ffffff00ff00ff00ff00ff00, cv5, cv4] 8 (Tr.N (Tr.N Tr.E [cv0, cv6, cv3, cv1, cv2, 0xffffff00ffffff00ffff0000ffff0000, cv5, cv4] 8 Tr.E) [cv0, cv6, cv3, cv1, cv2, 0xffffff00ffffff00ffffff00ffffff00, cv5, cv4] 9 Tr.E))) [cv0, cv6, cv3, cv1, cv2, 0xffffffaaffffffaaffffffaaffffffaa, cv5, cv4] 8 (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv0, cv6, cv3, cv1, cv2, 0xffffffccffffffccffffffccffffffcc, cv5, cv4] 8 Tr.E) [cv0, cv6, cv3, cv1, cv2, 0xfffffff0fffffff0fffffff0fffffff0, cv5, cv4] 8 (Tr.N Tr.E [cv0, cv6, cv3, cv1, cv2, cv42, cv15] 7 Tr.E)) [cv0, cv6, cv3, cv1, cv2, cv42, cv31] 7 (Tr.N (Tr.N Tr.E [cv0, cv6, cv3, cv1, cv2, cv42, 0xfffffffffffffffffafafafafafafafa] 6 Tr.E) [cv0, cv6, cv3, cv1, cv2, cv42, cv19] 7 Tr.E)) [cv0, cv6, cv3, cv1, cv2, cv5, cv36, cv4] 8 (Tr.N (Tr.N (Tr.N Tr.E [cv0, cv6, cv3, cv1, cv2, cv5, 0xffffffffff00ff00ff00ff00ff00ff00, cv4] 8 Tr.E) [cv0, cv6, cv3, cv1, cv2, cv5, cv27, cv4] 9 Tr.E) [cv0, cv6, cv3, cv1, cv2, cv5, 0xffffffffffaaffaaffffffffffaaffaa, cv4] 8 (Tr.N (Tr.N Tr.E [cv0, cv6, cv3, cv1, cv2, cv5, 0xffffffffffccffccffffffffffccffcc, cv4] 8 Tr.E) [cv0, cv6, cv3, cv1, cv2, cv5, 0xffffffffffeeffeeffffffffffeeffee, cv4] 7 Tr.E))))
def t79 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv0, cv6, cv3, cv1, cv2, cv5, 0xfffffffffffcfffcfffffffffffcfffc, cv4] 7 Tr.E) [cv0, cv6, cv3, cv1, cv2, cv5, 0xffffffffffff0000ffffffffffff0000, cv4] 9 (Tr.N Tr.E [cv0, cv6, cv3, cv1, cv2, cv5, 0xffffffffffffaaaaffffffffffffaaaa, cv4] 8 Tr.E)) [cv0, cv6, cv3, cv1, cv2, cv5, 0xffffffffffffeeeeffffffffffffeeee, cv4] 7 (Tr.N (Tr.N Tr.E [cv0, cv6, cv3, cv1, cv2, cv5, 0xfffffffffffff0f0fffffffffffff0f0, cv4] 8 Tr.E) [cv0, cv6, cv3, cv1, cv2, cv5, 0xffffffffffffff00ffffffffffffff00, cv4] 8 Tr.E)) [cv0, cv6, cv3, cv1, cv2, cv5, cv4] 10 (Tr.N (Tr.N (Tr.N Tr.E [cv0, cv6, cv3, cv1, cv2, cv5, cv4, cv45] 9 Tr.E) [cv0, cv6, cv3, cv1, cv2, cv5, cv4, 0xffffffffffffffffffaaffaaffaaffaa] 8 (Tr.N Tr.E [cv0, cv6, cv3, cv1, cv2, cv5, cv4, 0xfffffffffffffffffff0fff0fff0fff0] 8 Tr.E)) [cv0, cv6, cv3, cv1, cv2, cv5, cv4, 0xffffffffffffffffffffff00ffffff00] 8 (Tr.N (Tr.N Tr.E [cv0, cv6, cv3, cv1, cv2, cv5, cv4, 0xffffffffffffffffffffffffffffffff] 9 Tr.E) [cv0, cv6, cv3, cv1, cv2, cv5, 0xffffffffffffffff000000000000ffff] 7 Tr.E))) [cv0, cv6, cv3, cv1, cv2, cv5, 0xffffffffffffffff0000000033333333] 7 (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv0, cv6, cv3, cv1, cv2, cv5, 0xffffffffffffffff00000000aaaaaaaa] 7 Tr.E) [cv0, cv6, cv3, cv1, cv2, cv5, 0xffffffffffffffff00000000f0f0f0f0] 7 (Tr.N Tr.E [cv0, cv6, cv3, cv1, cv2, cv5, 0xffffffffffffffff00000000ff00ff00] 7 Tr.E)) [cv0, cv6, cv3, cv1, cv2, cv5, 0xffffffffffffffff00f000f000f000f0] 7 (Tr.N (Tr.N Tr.E [cv0, cv6, cv3, cv1, cv2, cv5, 0xffffffffffffffff3333000033330000] 7 Tr.E) [cv0, cv6, cv3, cv1, cv2, cv5, 0xffffffffffffffff8080808080808080] 7 Tr.E)) [cv0, cv6, cv3, cv1, cv2, cv5, 0xffffffffffffffff8800880088008800] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv0, cv6, cv3, cv1, cv2, cv5, 0xffffffffffffffff8888000088880000] 7 Tr.E) [cv0, cv6, cv3, cv1, cv2, cv5, 0xffffffffffffffff8888888800000000] 7 Tr.E) [cv0, cv6, cv3, cv1, cv2, cv5, 0xffffffffffffffff8888888888888888] 8 (Tr.N (Tr.N Tr.E [cv0, cv6, cv3, cv1, cv2, cv5, 0xffffffffffffffffa000a000a000a000] 7 Tr.E) [cv0, cv6, cv3, cv1, cv2, cv5, 0xffffffffffffffffa0a00000a0a00000] 7 Tr.E))))
def u80 : Tr := Tr.N t78 [cv0, cv6, cv3, cv1, cv2, cv5, 0xfffffffffff0fff0fffffffffff0fff0, cv4] 8 t79
def t81 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv0, cv6, cv3, cv1, cv2, cv5, 0xffffffffffffffffa0a0a0a0a0a0a0a0] 8 Tr.E) [cv0, cv6, cv3, cv1, cv2, cv5, 0xffffffffffffffffa8a8a8a8a8a8a8a8] 7 (Tr.N Tr.E [cv0, cv6, cv3, cv1, cv2, cv5, 0xffffffffffffffffaa000000aa000000] 7 Tr.E)) [cv0, cv6, cv3, cv1, cv2, cv5, 0xffffffffffffffffaa00aa0000000000] 7 (Tr.N (Tr.N Tr.E [cv0, cv6, cv3, cv1, cv2, cv5, 0xffffffffffffffffaa00aa00aa00aa00] 8 Tr.E) [cv0, cv6, cv3, cv1, cv2, cv5, 0xffffffffffffffffaa88aa88aa88aa88] 7 Tr.E)) [cv0, cv6, cv3, cv1, cv2, cv5, 0xffffffffffffffffaaa0aaa0aaa0aaa0] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv0, cv6, cv3, cv1, cv2, cv5, 0xffffffffffffffffaaaa000000000000] 7 Tr.E) [cv0, cv6, cv3, cv1, cv2, cv5, 0xffffffffffffffffaaaa0000aaaa0000] 8 (Tr.N Tr.E [cv0, cv6, cv3, cv1, cv2, cv5, 0xffffffffffffffffaaaa8888aaaa8888] 7 Tr.E)) [cv0, cv6, cv3, cv1, cv2, cv5, 0xffffffffffffffffaaaaa0a0aaaaa0a0] 7 (Tr.N (Tr.N Tr.E [cv0, cv6, cv3, cv1, cv2, cv5, 0xffffffffffffffffaaaaaa00aaaaaa00] 7 Tr.E) [cv0, cv6, cv3, cv1, cv2, cv5, cv15, 0xffffffffffffffffcccccccccccccccc] 8 Tr.E))) [cv0, cv6, cv3, cv1, cv2, cv5, cv15, cv31] 8 (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv0, cv6, cv3, cv1, cv2, cv5, cv15, cv45] 8 Tr.E) [cv0, cv6, cv3, cv1, cv2, cv5, cv15, cv35] 8 (Tr.N Tr.E [cv0, cv6, cv3, cv1, cv2, cv5, cv15, 0xffffffffffffffffffffccccffffcccc] 7 Tr.E)) [cv0, cv6, cv3, cv1, cv2, cv5, cv15, 0xfffffffffffffffffffff0f0fffff0f0] 7 (Tr.N (Tr.N Tr.E [cv0, cv6, cv3, cv1, cv2, cv5, 0xffffffffffffffffc000c000c000c000] 7 Tr.E) [cv0, cv6, cv3, cv1, cv2, cv5, 0xffffffffffffffffc0c00000c0c00000] 7 Tr.E)) [cv0, cv6, cv3, cv1, cv2, cv5, 0xffffffffffffffffc0c0c0c000000000] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv0, cv6, cv3, cv1, cv2, cv5, cv57] 8 Tr.E) [cv0, cv6, cv3, cv1, cv2, cv5, 0xffffffffffffffffc8c8c8c8c8c8c8c8] 7 Tr.E) [cv0, cv6, cv3, cv1, cv2, cv5, 0xffffffffffffffffcc000000cc000000] 7 (Tr.N (Tr.N Tr.E [cv0, cv6, cv3, cv1, cv2, cv5, 0xffffffffffffffffcccc000000000000] 7 Tr.E) [cv0, cv6, cv3, cv1, cv2, cv5, 0xffffffffffffffffcccccccccccccccc, cv31] 8 Tr.E))))
def t82 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv0, cv6, cv3, cv1, cv2, cv5, 0xfffffffffffffffff0000000f0000000] 7 Tr.E) [cv0, cv6, cv3, cv1, cv2, cv5, 0xfffffffffffffffff0f0000000000000] 7 (Tr.N Tr.E [cv0, cv6, cv3, cv1, cv2, cv5, 0xfffffffffffffffff0f00000f0f00000] 8 Tr.E)) [cv0, cv6, cv3, cv1, cv2, cv5, 0xfffffffffffffffff0f0a0a0f0f0a0a0] 7 (Tr.N (Tr.N Tr.E [cv0, cv6, cv3, cv1, cv2, cv5, 0xfffffffffffffffff0f0c0c0f0f0c0c0] 7 Tr.E) [cv0, cv6, cv3, cv1, cv2, cv5, cv31, cv35] 8 Tr.E)) [cv0, cv6, cv3, cv1, cv2, cv5, cv31, 0xffffffffffffffffffffaaaaffffaaaa] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv0, cv6, cv3, cv1, cv2, cv5, 0xfffffffffffffffffafa0000fafa0000] 7 Tr.E) [cv0, cv6, cv3, cv1, cv2, cv5, 0xfffffffffffffffffafafafafafafafa, cv35] 7 Tr.E) [cv0, cv6, cv3, cv1, cv2, cv5, 0xffffffffffffffffff00000000000000] 7 (Tr.N (Tr.N Tr.E [cv0, cv6, cv3, cv1, cv2, cv5, cv53] 8 Tr.E) [cv0, cv6, cv3, cv1, cv2, cv5, 0xffffffffffffffffff00aa00ff00aa00] 7 Tr.E))) [cv0, cv6, cv3, cv1, cv2, cv5, cv45, cv35] 8 (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv0, cv6, cv3, cv1, cv2, cv5, 0xffffffffffffffffffaa0000ffaa0000] 7 Tr.E) [cv0, cv6, cv3, cv1, cv2, cv5, 0xfffffffffffffffffff00000fff00000] 7 (Tr.N Tr.E [cv0, cv6, cv3, cv1, cv2, cv5, cv19] 8 Tr.E)) [cv0, cv6, cv3, cv1, cv2, cv5, 0xffffffffffffffffffff0000aaaa0000] 7 (Tr.N (Tr.N Tr.E [cv0, cv6, cv3, cv1, cv2, cv5, 0xffffffffffffffffffff0000f0f00000] 7 Tr.E) [cv0, cv6, cv3, cv1, cv2, cv5, 0xffffffffffffffffffff0000ff000000] 7 Tr.E)) [cv0, cv6, cv3, cv1, cv2, cv5, cv35, 0xffffffffffffffffffffffff00000000] 8 (Tr.N (Tr.N (Tr.N Tr.E [cv0, cv6, cv3, cv1, cv2, 0xffffffff00000000ffffffff0000ffff, cv4] 7 Tr.E) [cv0, cv6, cv3, cv1, cv2, 0xffffffff00000000ffffffff33333333, cv4] 7 Tr.E) [cv0, cv6, cv3, cv1, cv2, 0xffffffff00000000ffffffffaaaaaaaa, cv4] 7 (Tr.N (Tr.N Tr.E [cv0, cv6, cv3, cv1, cv2, 0xffffffff00000000fffffffff0f0f0f0, cv4] 7 Tr.E) [cv0, cv6, cv3, cv1, cv2, 0xffffffff00000000ffffffffff00ff00, cv4] 7 Tr.E))))
def u83 : Tr := Tr.N t81 [cv0, cv6, cv3, cv1, cv2, cv5, 0xffffffffffffffffe0e0e0e0e0e0e0e0] 7 t82
def u84 : Tr := Tr.N u80 [cv0, cv6, cv3, cv1, cv2, cv5, 0xffffffffffffffffa0a0a0a000000000] 7 u83
def t85 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv0, cv6, cv3, cv1, cv2, 0xffffffff00000f0fffffffff00000f0f, cv4] 7 Tr.E) [cv0, cv6, cv3, cv1, cv2, 0xffffffff0000aaaaffffffff0000aaaa, cv4] 7 (Tr.N Tr.E [cv0, cv6, cv3, cv1, cv2, 0xffffffff0000ccccffffffff0000cccc, cv4] 7 Tr.E)) [cv0, cv6, cv3, cv1, cv2, 0xffffffff0f000f00ffffffff0f000f00, cv4] 7 (Tr.N (Tr.N Tr.E [cv0, cv6, cv3, cv1, cv2, 0xffffffff80808080ffffffff80808080, cv4] 7 Tr.E) [cv0, cv6, cv3, cv1, cv2, 0xffffffff88008800ffffffff88008800, cv4] 7 Tr.E)) [cv0, cv6, cv3, cv1, cv2, 0xffffffff88880000ffffffff88880000, cv4] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv0, cv6, cv3, cv1, cv2, 0xffffffff88888888ffffffff00000000, cv4] 7 Tr.E) [cv0, cv6, cv3, cv1, cv2, cv59, cv4] 8 (Tr.N Tr.E [cv0, cv6, cv3, cv1, cv2, cv59, cv4, cv45] 7 Tr.E)) [cv0, cv6, cv3, cv1, cv2, cv59, 0xffffffffffffffff8888888888888888] 7 (Tr.N (Tr.N Tr.E [cv0, cv6, cv3, cv1, cv2, 0xffffffffa000a000ffffffffa000a000, cv4] 7 Tr.E) [cv0, cv6, cv3, cv1, cv2, 0xffffffffa0a00000ffffffffa0a00000, cv4] 7 Tr.E))) [cv0, cv6, cv3, cv1, cv2, 0xffffffffa0a0a0a0ffffffff00000000, cv4] 7 (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv0, cv6, cv3, cv1, cv2, 0xffffffffa0a0a0a0ffffffffa0a0a0a0, cv4] 8 Tr.E) [cv0, cv6, cv3, cv1, cv2, 0xffffffffa0a0a0a0ffffffffa0a0a0a0, 0xffffffffffffffffa0a0a0a0a0a0a0a0] 7 (Tr.N Tr.E [cv0, cv6, cv3, cv1, cv2, 0xffffffffa8a8a8a8ffffffffa8a8a8a8, cv4] 7 Tr.E)) [cv0, cv6, cv3, cv1, cv2, 0xffffffffaa000000ffffffffaa000000, cv4] 7 (Tr.N (Tr.N Tr.E [cv0, cv6, cv3, cv1, cv2, 0xffffffffaa00aa00ffffffff00000000, cv4] 7 Tr.E) [cv0, cv6, cv3, cv1, cv2, 0xffffffffaa00aa00ffffffffaa00aa00, cv4] 8 Tr.E)) [cv0, cv6, cv3, cv1, cv2, 0xffffffffaa00aa00ffffffffaa00aa00, 0xffffffffffffffffaa00aa00aa00aa00] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv0, cv6, cv3, cv1, cv2, 0xffffffffaa88aa88ffffffffaa88aa88, cv4] 7 Tr.E) [cv0, cv6, cv3, cv1, cv2, 0xffffffffaaa0aaa0ffffffffaaa0aaa0, cv4] 7 Tr.E) [cv0, cv6, cv3, cv1, cv2, cv13, cv24, cv4] 8 (Tr.N (Tr.N Tr.E [cv0, cv6, cv3, cv1, cv2, cv13, 0xfffffffff0f0f0f0fffffffff0f0f0f0, cv4] 8 Tr.E) [cv0, cv6, cv3, cv1, cv2, cv13, cv27, cv4] 8 Tr.E))))
def t86 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv0, cv6, cv3, cv1, cv2, 0xffffffffc000c000ffffffffc000c000, cv4] 7 Tr.E) [cv0, cv6, cv3, cv1, cv2, 0xffffffffc0c00000ffffffffc0c00000, cv4] 7 (Tr.N Tr.E [cv0, cv6, cv3, cv1, cv2, 0xffffffffc0c0c0c0ffffffff00000000, cv4] 7 Tr.E)) [cv0, cv6, cv3, cv1, cv2, 0xffffffffc0c0c0c0ffffffffc0c0c0c0, cv4] 8 (Tr.N (Tr.N Tr.E [cv0, cv6, cv3, cv1, cv2, 0xffffffffc0c0c0c0ffffffffc0c0c0c0, cv57] 7 Tr.E) [cv0, cv6, cv3, cv1, cv2, 0xffffffffc8c8c8c8ffffffffc8c8c8c8, cv4] 7 Tr.E)) [cv0, cv6, cv3, cv1, cv2, 0xffffffffcc000000ffffffffcc000000, cv4] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv0, cv6, cv3, cv1, cv2, 0xffffffffcc00cc00ffffffff00000000, cv4] 7 Tr.E) [cv0, cv6, cv3, cv1, cv2, 0xffffffffcc00cc00ffffffffcc00cc00, cv4] 8 Tr.E) [cv0, cv6, cv3, cv1, cv2, 0xffffffffcc88cc88ffffffffcc88cc88, cv4] 7 (Tr.N (Tr.N Tr.E [cv0, cv6, cv3, cv1, cv2, 0xffffffffccc0ccc0ffffffffccc0ccc0, cv4] 7 Tr.E) [cv0, cv6, cv3, cv1, cv2, 0xffffffffcccc0000ffffffff00000000, cv4] 7 Tr.E))) [cv0, cv6, cv3, cv1, cv2, 0xffffffffccccccccffff000000000000] 6 (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv0, cv6, cv3, cv1, cv2, 0xffffffffccccccccffffffff00000000, cv4] 8 Tr.E) [cv0, cv6, cv3, cv1, cv2, 0xffffffffccccccccffffffff00000000, cv35] 7 (Tr.N Tr.E [cv0, cv6, cv3, cv1, cv2, 0xffffffffccccccccffffffff88888888, cv4] 7 Tr.E)) [cv0, cv6, cv3, cv1, cv2, 0xffffffffccccccccffffffffc0c0c0c0, cv4] 7 (Tr.N (Tr.N Tr.E [cv0, cv6, cv3, cv1, cv2, 0xffffffffccccccccffffffffcc00cc00, cv4] 7 Tr.E) [cv0, cv6, cv3, cv1, cv2, cv24, 0xfffffffff0f0f0f0fffffffff0f0f0f0, cv4] 8 Tr.E)) [cv0, cv6, cv3, cv1, cv2, cv24, cv27, cv4] 8 (Tr.N (Tr.N (Tr.N Tr.E [cv0, cv6, cv3, cv1, cv2, cv24, 0xffffffffffaaffaaffffffffffaaffaa, cv4] 7 Tr.E) [cv0, cv6, cv3, cv1, cv2, cv24, 0xfffffffffff0fff0fffffffffff0fff0, cv4] 7 Tr.E) [cv0, cv6, cv3, cv1, cv2, cv24, cv4, 0xffffffffffffffffffffffff00000000] 8 (Tr.N (Tr.N Tr.E [cv0, cv6, cv3, cv1, cv2, cv24, cv19] 7 Tr.E) [cv0, cv6, cv3, cv1, cv2, 0xffffffffe0e0e0e0ffffffffe0e0e0e0, cv4] 7 Tr.E))))
def u87 : Tr := Tr.N t85 [cv0, cv6, cv3, cv1, cv2, cv13, 0xffffffffffccffccffffffffffccffcc, cv4] 7 t86
def t88 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv0, cv6, cv3, cv1, cv2, 0xffffffffeeeeeeeeffffffffeeeeeeee, cv27, cv4] 7 Tr.E) [cv0, cv6, cv3, cv1, cv2, 0xfffffffff0000000fffffffff0000000, cv4] 7 (Tr.N Tr.E [cv0, cv6, cv3, cv1, cv2, 0xffffffffff000000ffffffff00000000, cv4] 7 Tr.E)) [cv0, cv6, cv3, cv1, cv2, cv36, cv4] 8 (Tr.N (Tr.N Tr.E [cv0, cv6, cv3, cv1, cv2, cv36, cv53] 7 Tr.E) [cv0, cv6, cv3, cv1, cv2, 0xffffffffff00aa00ffffffffff00aa00, cv4] 7 Tr.E)) [cv0, cv6, cv3, cv1, cv2, 0xffffffffff00cc00ffffffffff00cc00, cv4] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv0, cv6, cv3, cv1, cv2, cv27, 0xffffffffffff0000ffffffffffff0000, cv4] 8 Tr.E) [cv0, cv6, cv3, cv1, 0xffff8888ffff8888ffff8888ffff8888, cv5, 0xffffffffffffffff8888888888888888] 7 (Tr.N Tr.E [cv0, cv6, cv3, cv1, 0xffff8888ffff8888ffff8888ffff8888, cv59, cv4] 7 Tr.E)) [cv0, cv6, cv3, cv1, 0xffffa0a0ffffa0a0ffffa0a0ffffa0a0, cv5, 0xffffffffffffffffa0a0a0a0a0a0a0a0] 7 (Tr.N (Tr.N Tr.E [cv0, cv6, cv3, cv1, 0xffffa0a0ffffa0a0ffffa0a0ffffa0a0, 0xffffffffa0a0a0a0ffffffffa0a0a0a0, cv4] 7 Tr.E) [cv0, cv6, cv3, cv1, cv55, cv5, 0xffffffffffffffffaa00aa00aa00aa00] 7 Tr.E))) [cv0, cv6, cv3, cv1, cv55, 0xffffffffaa00aa00ffffffffaa00aa00, cv4] 7 (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv0, cv6, cv3, cv1, 0xffffaaaaffffaaaaffff0000ffff0000, cv5, cv15] 7 Tr.E) [cv0, cv6, cv3, cv1, cv23, cv42, cv31] 6 (Tr.N Tr.E [cv0, cv6, cv3, cv1, cv23, cv5, 0xffffffffffffffffaaaa0000aaaa0000] 7 Tr.E)) [cv0, cv6, cv3, cv1, cv23, cv5, cv31, cv35] 7 (Tr.N (Tr.N Tr.E [cv0, cv6, cv3, cv1, cv23, cv5, cv19] 7 Tr.E) [cv0, cv6, cv3, cv1, cv23, cv24, cv19] 6 Tr.E)) [cv0, cv6, cv3, cv1, 0xffffc0c0ffffc0c0ffffc0c0ffffc0c0, cv5, cv57] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv0, cv6, cv3, cv1, cv25, cv5, cv15, cv35] 7 Tr.E) [cv0, cv6, cv3, cv1, cv25, cv5, cv53] 7 Tr.E) [cv0, cv6, cv3, cv1, cv25, cv5, cv19] 7 (Tr.N (Tr.N Tr.E [cv0, cv6, cv3, cv1, 0xffffeeeeffffeeeeffffeeeeffffeeee, cv5, cv19] 6 Tr.E) [cv0, cv6, cv3, cv1, cv5, cv51, cv15] 7 Tr.E))))
def t89 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv0, cv6, cv3, cv1, cv5, cv51, 0xfffffffffffffffffafafafafafafafa] 6 Tr.E) [cv0, cv6, cv3, cv1, cv5, cv51, cv45] 7 (Tr.N Tr.E [cv0, cv6, cv3, cv1, cv5, cv51, 0xffffffffffffffffffffffff00000000] 7 Tr.E)) [cv0, cv6, cv3, cv1, cv5, 0xffffffffffff0000ffffffffffff0000, cv19] 7 (Tr.N (Tr.N Tr.E [cv0, cv6, cv3, cv1, 0xffffffffccccccccffffffff00000000, 0xffffffffffffccccffff0000ffff0000] 6 Tr.E) [cv0, cv6, cv3, cv1, 0xffffffffff000000ffff0000ff000000, cv4] 6 Tr.E)) [cv0, cv6, cv3, cv1, cv36, cv4, cv35] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv0, cv6, cv3, cv1, cv36, 0xffffffffffffffffffff0000ff000000] 6 Tr.E) [cv0, cv6, cv3, cv1, 0xffffffffffccccccffff0000ff000000] 5 Tr.E) [cv0, cv6, cv3, 0xff88ff88ff88ff88ff88ff88ff88ff88, cv2, cv5, 0xffffffffffffffff8888888888888888] 7 (Tr.N (Tr.N Tr.E [cv0, cv6, cv3, 0xffa0ffa0ffa0ffa0ffa0ffa0ffa0ffa0, cv2, cv5, 0xffffffffffffffffa0a0a0a0a0a0a0a0] 7 Tr.E) [cv0, cv6, cv3, 0xffccffccffccffccff00ff00ff00ff00, cv2, cv5, cv35] 7 Tr.E))) [cv0, cv6, cv3, 0xffccffccffccffccff00ff00ff00ff00, cv5, cv51] 6 (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv0, cv6, cv3, cv16, cv2, cv5, cv53] 7 Tr.E) [cv0, cv6, cv3, cv2, cv56, cv5, cv19] 7 (Tr.N Tr.E [cv0, cv6, cv3, cv2, 0xffffffffff00aa00ffffffffff00aa00, 0xffffffffffffffffff00aa00ff00aa00] 6 Tr.E)) [cv0, cv6, 0xf0f0f0f0f0f0fffff0f0f0f0f0f0ffff, cv1, cv2, cv5, cv4] 7 (Tr.N (Tr.N Tr.E [cv0, cv6, 0xf0f0f0f0fff0fff0f0f0f0f0fff0fff0, cv1, cv2, cv5, cv4] 7 Tr.E) [cv0, cv6, 0xf1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1, cv1, cv2, cv5, cv4] 7 Tr.E)) [cv0, cv6, 0xf3f0f3f0f3f0f3f0f3f0f3f0f3f0f3f0, cv1, cv2, cv5, cv4] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv0, cv6, 0xf8f0f8f0f8f0f8f0f8f0f8f0f8f0f8f0, cv1, cv2, cv5, cv4] 7 Tr.E) [cv0, cv6, 0xf8f8f0f0f8f8f0f0f8f8f0f0f8f8f0f0, cv1, cv2, cv5, cv4] 7 Tr.E) [cv0, cv6, 0xf8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8, cv1, cv2, cv5, cv4] 8 (Tr.N (Tr.N Tr.E [cv0, cv6, 0xf8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8, cv1, cv2, cv5, 0xffffffffffffffff8888888888888888] 7 Tr.E) [cv0, cv6, 0xf8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8, cv1, cv2, cv59, cv4] 7 Tr.E))))
def u90 : Tr := Tr.N t88 [cv0, cv6, cv3, cv1, cv5, cv51, cv31] 7 t89
def u91 : Tr := Tr.N u87 [cv0, cv6, cv3, cv1, cv2, 0xffffffffee00ee00ffffffffee00ee00, cv4] 7 u90
def u92 : Tr := Tr.N u84 [cv0, cv6, cv3, cv1, cv2, 0xffffffff000000ffffffffff000000ff, cv4] 7 u91
def u93 : Tr := Tr.N u77 [cv0, cv6, cv3, cv1, cv2, cv25, cv5, cv4] 9 u92
def t94 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv0, cv6, 0xfaf0faf0f0f0f0f0faf0faf0f0f0f0f0, cv1, cv2, cv5, cv4] 7 Tr.E) [cv0, cv6, 0xfaf0faf0faf0faf0f0f0f0f0f0f0f0f0, cv1, cv2, cv5, cv4] 7 (Tr.N Tr.E [cv0, cv6, cv38, cv22, cv2, cv5, cv4] 7 Tr.E)) [cv0, cv6, cv38, cv1, cv2, cv5, cv24, cv4] 7 (Tr.N (Tr.N Tr.E [cv0, cv6, cv38, cv1, cv2, cv5, cv4] 8 Tr.E) [cv0, cv6, cv38, cv1, cv2, cv5, 0xffffffffffffffffaa00aa00aa00aa00] 7 Tr.E)) [cv0, cv6, cv38, cv1, cv2, 0xffffffffaa00aa00ffffffffaa00aa00, cv4] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv0, cv6, cv38, cv1, cv55, cv5, cv4] 7 Tr.E) [cv0, cv6, cv38, cv58, cv2, cv5, cv4] 7 (Tr.N Tr.E [cv0, cv6, cv38, cv17, cv5, cv4] 6 Tr.E)) [cv0, cv6, cv38, cv17, cv24, cv4] 5 (Tr.N (Tr.N Tr.E [cv0, cv6, cv38, cv2, cv5, cv27, cv4] 7 Tr.E) [cv0, cv6, cv38, cv2, cv24, cv27, cv4] 6 Tr.E))) [cv0, cv6, cv38, cv2, cv36, cv4] 6 (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv0, cv6, 0xfaf8faf8faf8faf8faf8faf8faf8faf8, cv1, cv2, cv5, cv4] 7 Tr.E) [cv0, cv6, 0xfafaf0f0f0f0f0f0fafaf0f0f0f0f0f0, cv1, cv2, cv5, cv4] 7 (Tr.N Tr.E [cv0, cv6, 0xfafafafaf0f0f0f0f0f0f0f0f0f0f0f0, cv1, cv2, cv5, cv4] 7 Tr.E)) [cv0, cv6, cv41, 0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc, cv1, cv2, cv5, cv4] 8 (Tr.N (Tr.N Tr.E [cv0, cv6, cv41, cv1, cv28, cv2, cv5, cv4] 8 Tr.E) [cv0, cv6, cv41, 0xffa0ffa0ffa0ffa0ffa0ffa0ffa0ffa0, cv2, cv5, cv4] 7 Tr.E)) [cv0, cv6, cv22, cv1, cv46, cv2, cv5, cv4] 8 (Tr.N (Tr.N (Tr.N Tr.E [cv0, cv6, cv22, cv1, cv20, cv5, cv4] 7 Tr.E) [cv0, cv6, cv22, cv1, cv20, cv24, cv4] 6 Tr.E) [cv0, cv6, cv22, cv16, cv20, cv5, cv4] 6 (Tr.N (Tr.N Tr.E [cv0, cv6, cv40, 0xfff0faf0fff0faf0fff0faf0fff0faf0, cv2, cv5, cv4] 7 Tr.E) [cv0, cv6, 0xff00ff00ff00ff000000000000000000, cv1, 0xfff0fff0fff0fff0f0f0f0f0f0f0f0f0, cv2, cv5, cv4] 8 Tr.E))))
def t95 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv0, cv6, cv1, 0xff0fff0fff0fff0f0f0f0f0f0f0f0f0f, cv2, cv5, cv4] 7 Tr.E) [cv0, cv6, cv1, cv16, cv2, cv20, cv5, cv4] 7 (Tr.N Tr.E [cv0, cv6, cv1, cv16, cv2, cv5, 0xfffffffff0f0f0f0f0f0f0f0f0f0f0f0, cv4] 7 Tr.E)) [cv0, cv6, cv1, 0xfff0f0f0f0f0f0f0fff0f0f0f0f0f0f0, cv2, cv5, cv4] 7 (Tr.N (Tr.N Tr.E [cv0, cv6, cv1, 0xfff0f0f0fff0f0f0f0f0f0f0f0f0f0f0, cv2, cv5, cv4] 7 Tr.E) [cv0, cv6, cv1, cv46, cv2, cv5, cv4] 8 Tr.E)) [cv0, cv6, cv1, cv46, cv2, cv5, cv53] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv0, cv6, cv1, cv46, cv2, cv36, cv4] 7 Tr.E) [cv0, cv6, cv1, cv46, cv25, cv5, cv4] 7 (Tr.N Tr.E [cv0, cv6, cv1, cv46, cv25, cv5, cv53] 6 Tr.E)) [cv0, cv6, cv1, cv46, cv25, cv36, cv4] 6 (Tr.N (Tr.N Tr.E [cv0, cv6, cv1, 0xfff0faf0fff0faf0fff0faf0fff0faf0, cv2, cv5, cv4] 7 Tr.E) [cv0, cv6, cv1, 0xfff0fff0fff0fff0f0f0f0f0f0f0f0f0, cv2, cv5, cv4] 8 Tr.E))) [cv0, cv6, cv1, 0xfff0fff0fff0fff0faf0faf0faf0faf0, cv2, cv5, cv4] 7 (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv0, cv6, cv1, 0xfff0fff0fff0fff0fff0f0f0fff0f0f0, cv2, cv5, cv4] 7 Tr.E) [cv0, cv6, cv1, cv28, cv2, cv50, cv5, cv4] 8 (Tr.N Tr.E [cv0, cv6, cv1, cv28, cv2, cv5, cv4, cv31] 8 Tr.E)) [cv0, cv6, cv1, cv28, cv2, cv5, cv57] 7 (Tr.N (Tr.N Tr.E [cv0, cv6, cv1, cv28, 0xffffc0c0ffffc0c0ffffc0c0ffffc0c0, cv5, cv4] 7 Tr.E) [cv0, cv6, cv1, cv26, cv2, cv20, cv5, cv4] 8 Tr.E)) [cv0, cv6, cv1, 0xffff0000f0f00000ffff0000f0f00000, cv20, cv5, cv4] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv0, cv6, cv1, cv17, cv32, cv5, cv4] 7 Tr.E) [cv0, cv6, cv1, cv17, cv32, cv24, cv4] 6 Tr.E) [cv0, cv6, cv1, cv2, 0xffff0f0f0f0f0f0fffff0f0f0f0f0f0f, cv5, cv4] 7 (Tr.N (Tr.N Tr.E [cv0, cv6, cv1, cv2, cv20, cv5, cv4] 8 Tr.E) [cv0, cv6, cv1, cv2, cv20, cv5, cv19] 7 Tr.E))))
def u96 : Tr := Tr.N t94 [cv0, cv6, cv1, 0xff0f0f0fff0f0f0fff0f0f0fff0f0f0f, cv2, cv5, cv4] 7 t95
def t97 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv0, cv6, cv1, cv2, cv20, cv13, cv19] 6 Tr.E) [cv0, cv6, cv1, cv2, cv20, cv24, cv4] 7 (Tr.N Tr.E [cv0, cv6, cv1, cv2, cv20, 0xffffffffeeeeeeeeffffffffeeeeeeee, cv4] 6 Tr.E)) [cv0, cv6, cv1, cv2, cv32, cv5, cv4] 7 (Tr.N (Tr.N Tr.E [cv0, cv6, cv1, cv2, cv50, cv5, 0xfffffffff0f0f0f0fffffffff0f0f0f0, cv4] 8 Tr.E) [cv0, cv6, cv1, cv2, cv42, 0xfffffffff0f0f0f0fffff0f0f0f0f0f0, cv15] 6 Tr.E)) [cv0, cv6, cv1, cv2, cv5, 0xfffffffff0f0f0f0f0f0f0f0f0f0f0f0, cv15] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv0, cv6, cv1, cv2, cv5, 0xfffffffff0f0f0f0fffff0f0f0f0f0f0, cv15] 6 Tr.E) [cv0, cv6, cv1, cv2, cv44, 0xfffffffff0f0f0f0fffff0f0f0f0f0f0, cv4] 6 (Tr.N Tr.E [cv0, cv6, cv1, cv2, 0xffffffffe0e0e0e0ffffffffe0e0e0e0, 0xffffffffffffffffe0e0e0e0e0e0e0e0] 6 Tr.E)) [cv0, cv6, cv1, cv23, cv20, cv5, cv19] 6 (Tr.N (Tr.N Tr.E [cv0, cv6, cv1, cv23, cv20, cv24, cv4] 6 Tr.E) [cv0, cv6, cv1, cv25, cv20, cv13, cv4] 6 Tr.E))) [cv0, cv6, cv1, 0xffffe0e0ffffe0e0ffffe0e0ffffe0e0, 0xffffffffe0e0e0e0ffffffffe0e0e0e0, cv4] 6 (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv0, cv6, cv1, cv5, 0xfffffffff0f0f0f0f0f0f0f0f0f0f0f0, cv51, cv15] 6 Tr.E) [cv0, cv6, cv1, cv5, 0xfffffffffcfcfcfcf0f0f0f0f0f0f0f0, 0xffffffffffffccccffff0000ffff0000] 6 (Tr.N Tr.E [cv0, cv6, 0xffa0ffa0ffa0ffa0ffa0ffa0ffa0ffa0, cv2, cv5, cv57] 6 Tr.E)) [cv0, cv6, cv16, cv46, cv2, cv5, cv53] 6 (Tr.N (Tr.N Tr.E [cv0, cv6, 0xffe0ffe0ffe0ffe0ffe0ffe0ffe0ffe0, cv2, cv5, 0xffffffffffffffffe0e0e0e0e0e0e0e0] 6 Tr.E) [cv0, 0xccccccccccccccccccccccccffffffff, cv3, cv1, cv2, cv5, cv4] 7 Tr.E)) [cv0, 0xccccccccccccccccffffccccffffcccc, cv3, cv1, cv2, cv5, cv4] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv0, 0xcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcd, cv3, cv1, cv2, cv5, cv4] 7 Tr.E) [cv0, 0xcfcccfcccfcccfcccfcccfcccfcccfcc, cv3, cv1, cv2, cv5, cv4] 7 Tr.E) [cv0, 0xe0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0, cv47, cv1, cv2, cv5, cv4] 7 (Tr.N (Tr.N Tr.E [cv0, 0xeccceccceccceccceccceccceccceccc, cv3, cv1, cv2, cv5, cv4] 7 Tr.E) [cv0, 0xececccccececccccececccccececcccc, cv3, cv1, cv2, cv5, cv4] 7 Tr.E))))
def t98 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv0, 0xececececececececcccccccccccccccc, cv3, cv1, cv2, cv5, cv4] 7 Tr.E) [cv0, cv47, cv3, cv1, cv17, cv5, cv4] 6 (Tr.N Tr.E [cv0, cv47, cv3, cv1, cv2, cv5, cv27, cv4] 7 Tr.E)) [cv0, cv47, cv3, cv1, cv2, cv5, cv4] 8 (Tr.N (Tr.N Tr.E [cv0, cv47, cv3, cv1, cv2, cv5, 0xffffffffffffffffa0a0a0a0a0a0a0a0] 7 Tr.E) [cv0, cv47, cv3, cv1, cv2, 0xffffffffa0a0a0a0ffffffffa0a0a0a0, cv4] 7 Tr.E)) [cv0, cv47, cv3, cv1, 0xffffa0a0ffffa0a0ffffa0a0ffffa0a0, cv5, cv4] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv0, cv47, cv3, 0xffa0ffa0ffa0ffa0ffa0ffa0ffa0ffa0, cv2, cv5, cv4] 7 Tr.E) [cv0, cv47, cv41, cv1, cv2, cv5, cv4] 7 Tr.E) [cv0, cv47, cv1, cv2, cv5, cv4, cv31] 7 (Tr.N (Tr.N Tr.E [cv0, cv47, cv1, cv2, cv5, cv57] 6 Tr.E) [cv0, cv47, cv1, cv2, cv5, 0xffffffffffffffffe0e0e0e0e0e0e0e0] 6 Tr.E))) [cv0, 0xeecccccceecccccceecccccceecccccc, cv3, cv1, cv2, cv5, cv4] 7 (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv0, 0xeecceecccccccccceecceecccccccccc, cv3, cv1, cv2, cv5, cv4] 7 Tr.E) [cv0, 0xeecceecceecceecccccccccccccccccc, cv3, cv1, cv2, cv5, cv4] 7 (Tr.N Tr.E [cv0, cv29, cv3, cv22, cv2, cv5, cv4] 7 Tr.E)) [cv0, cv29, cv3, cv1, cv2, cv5, cv13, cv4] 7 (Tr.N (Tr.N Tr.E [cv0, cv29, cv3, cv1, cv2, cv5, 0xfffffffff0f0f0f0fffffffff0f0f0f0, cv4] 7 Tr.E) [cv0, cv29, cv3, cv1, cv2, cv5, cv4] 8 Tr.E)) [cv0, cv29, cv3, cv1, cv2, cv5, 0xffffffffffffffffaa00aa00aa00aa00] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv0, cv29, cv3, cv1, cv2, 0xffffffffaa00aa00ffffffffaa00aa00, cv4] 7 Tr.E) [cv0, cv29, cv3, cv1, cv55, cv5, cv4] 7 Tr.E) [cv0, cv29, cv3, cv58, cv2, cv5, cv4] 7 (Tr.N (Tr.N Tr.E [cv0, cv29, cv3, cv58, cv2, 0xffffffffaa00aa00ffffffffaa00aa00, cv4] 6 Tr.E) [cv0, cv29, cv3, cv17, cv5, cv4] 6 Tr.E))))
def u99 : Tr := Tr.N t97 [cv0, 0xececececccccccccececececcccccccc, cv3, cv1, cv2, cv5, cv4] 7 t98
def u100 : Tr := Tr.N u96 [cv0, cv6, cv1, cv2, cv20, cv13, cv4] 7 u99
def t101 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv0, cv29, cv3, cv2, cv5, 0xffffffffffaaffaaffffffffffaaffaa, cv4] 6 Tr.E) [cv0, cv29, cv3, cv2, cv13, cv27, cv4] 6 (Tr.N Tr.E [cv0, cv29, cv3, cv2, cv36, cv4] 6 Tr.E)) [cv0, cv29, cv38, cv1, cv2, cv5, cv4] 7 (Tr.N (Tr.N Tr.E [cv0, cv29, cv38, cv17, cv5, cv4] 5 Tr.E) [cv0, cv29, cv38, cv2, cv5, cv27, cv4] 6 Tr.E)) [cv0, cv29, cv17, cv32, cv5, cv4] 5 (Tr.N (Tr.N (Tr.N Tr.E [cv0, 0xeeeceeeceeeceeeceeeceeeceeeceeec, cv3, cv1, cv2, cv5, cv4] 7 Tr.E) [cv0, 0xeeeceeeceeeceeeceeeceeeceeeceeec, cv3, cv17, cv5, cv4] 5 (Tr.N Tr.E [cv0, 0xeeeceeeceeeceeeceeeceeeceeeceeec, cv3, cv2, cv5, cv27, cv4] 6 Tr.E)) [cv0, 0xeeeecccccccccccceeeecccccccccccc, cv3, cv1, cv2, cv5, cv4] 7 (Tr.N (Tr.N Tr.E [cv0, 0xeeeecccccccccccceeeecccccccccccc, cv3, cv1, cv2, cv13, cv4] 6 Tr.E) [cv0, 0xeeeeeeeecccccccccccccccccccccccc, cv3, cv1, cv2, cv5, cv4] 7 Tr.E))) [cv0, cv33, cv3, 0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc, cv1, cv2, cv5, cv4] 8 (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv0, cv33, cv3, cv1, cv16, cv2, cv5, cv4] 8 Tr.E) [cv0, cv33, cv3, cv1, 0xffff8888ffff8888ffff8888ffff8888, cv59, cv4] 6 (Tr.N Tr.E [cv0, cv33, cv3, 0xff88ff88ff88ff88ff88ff88ff88ff88, cv2, cv5, cv4] 7 Tr.E)) [cv0, cv33, cv3, 0xff88ff88ff88ff88ff88ff88ff88ff88, cv2, cv59, cv4] 6 (Tr.N (Tr.N Tr.E [cv0, cv33, cv3, cv16, cv17, cv5, cv4] 6 Tr.E) [cv0, cv33, cv3, cv16, cv2, cv5, cv27, cv4] 7 Tr.E)) [cv0, cv33, cv3, cv16, cv2, 0xffffffffcc00cc00ffffffffcc00cc00, cv4] 6 (Tr.N (Tr.N (Tr.N Tr.E [cv0, cv33, cv3, cv16, cv2, cv36, cv4] 6 Tr.E) [cv0, cv33, 0xf8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8, cv1, cv2, cv5, cv4] 7 Tr.E) [cv0, cv3, 0xfcccccccfcccccccfcccccccfccccccc, cv1, cv2, cv5, cv4] 7 (Tr.N (Tr.N Tr.E [cv0, cv3, 0xfcfcccccccccccccfcfccccccccccccc, cv1, cv2, cv5, cv4] 7 Tr.E) [cv0, cv3, 0xfcfcfcfccccccccccccccccccccccccc, cv1, cv2, cv5, cv4] 7 Tr.E))))
def t102 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv0, cv3, cv22, cv1, cv12, cv5, cv4] 7 Tr.E) [cv0, cv3, cv40, 0xffcceeccffcceeccffcceeccffcceecc, cv2, cv5, cv4] 7 (Tr.N Tr.E [cv0, cv3, cv1, 0xff333333ff333333ff333333ff333333, cv2, cv5, cv4] 7 Tr.E)) [cv0, cv3, cv1, cv58, cv2, cv5, cv11, cv4] 7 (Tr.N (Tr.N Tr.E [cv0, cv3, cv1, 0xffccccccccccccccffcccccccccccccc, cv2, cv5, cv4] 7 Tr.E) [cv0, cv3, cv1, 0xffccccccffcccccccccccccccccccccc, cv2, cv5, cv4] 7 Tr.E)) [cv0, cv3, cv1, cv14, cv26, cv5, cv4] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv0, cv3, cv1, cv14, cv2, cv5, cv13, cv4] 7 Tr.E) [cv0, cv3, cv1, cv14, cv2, cv5, cv4] 8 Tr.E) [cv0, cv3, cv1, cv14, cv2, cv5, cv4, cv15] 7 (Tr.N (Tr.N Tr.E [cv0, cv3, cv1, cv14, cv2, cv5, cv53] 7 Tr.E) [cv0, cv3, cv1, cv14, cv2, cv36, cv4] 7 Tr.E))) [cv0, cv3, cv1, cv14, cv50, cv5, cv4] 7 (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv0, cv3, cv1, cv14, cv50, cv5, cv53] 6 Tr.E) [cv0, cv3, cv1, cv14, cv50, cv36, cv4] 6 (Tr.N Tr.E [cv0, cv3, cv1, cv14, cv5, cv4, cv35] 7 Tr.E)) [cv0, cv3, cv1, cv14, cv5, cv15, cv35] 6 (Tr.N (Tr.N Tr.E [cv0, cv3, cv1, cv14, cv5, cv19] 6 Tr.E) [cv0, cv3, cv1, 0xffcceeccffcceeccffcceeccffcceecc, cv2, cv5, cv4] 7 Tr.E)) [cv0, cv3, cv1, 0xffccffcccccccccccccccccccccccccc, cv2, cv5, cv4] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv0, cv3, cv1, cv16, cv2, cv25, cv5, cv4] 8 Tr.E) [cv0, cv3, cv1, cv16, cv2, 0xffffffffc0c0c0c0ffffffffc0c0c0c0, cv57] 6 Tr.E) [cv0, cv3, cv1, cv16, 0xffffc0c0ffffc0c0ffffc0c0ffffc0c0, cv5, cv4] 7 (Tr.N (Tr.N Tr.E [cv0, cv3, cv1, cv16, 0xffffc0c0ffffc0c0ffffc0c0ffffc0c0, cv5, cv57] 6 Tr.E) [cv0, cv3, cv1, cv16, 0xffffc0c0ffffc0c0ffffc0c0ffffc0c0, 0xffffffffc0c0c0c0ffffffffc0c0c0c0, cv4] 6 Tr.E))))
def u103 : Tr := Tr.N t101 [cv0, cv3, cv22, cv1, cv14, cv2, cv5, cv4] 8 t102
def t104 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv0, cv3, cv1, cv26, cv2, cv12, cv5, cv4] 8 Tr.E) [cv0, cv3, cv1, cv26, cv2, cv12, cv13, cv4] 7 (Tr.N Tr.E [cv0, cv3, cv1, cv26, cv2, cv11, cv4] 7 Tr.E)) [cv0, cv3, cv1, cv26, cv2, cv11, cv15] 6 (Tr.N (Tr.N Tr.E [cv0, cv3, cv1, cv26, cv23, cv12, cv5, cv4] 7 Tr.E) [cv0, cv3, cv1, cv26, cv23, cv11, cv4] 6 Tr.E)) [cv0, cv3, cv1, cv17, cv21, cv5, cv4] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv0, cv3, cv1, cv17, cv11, cv4] 6 Tr.E) [cv0, cv3, cv1, cv17, cv11, cv15] 5 (Tr.N Tr.E [cv0, cv3, cv1, cv17, cv11, cv31] 5 Tr.E)) [cv0, cv3, cv1, cv2, 0xffff333333333333ffff333333333333, cv5, cv4] 7 (Tr.N (Tr.N Tr.E [cv0, cv3, cv1, cv2, cv30, cv12, cv5, cv4] 7 Tr.E) [cv0, cv3, cv1, cv2, cv23, cv5, cv11, cv4] 7 Tr.E))) [cv0, cv3, cv1, cv2, 0xffffcccccccccccccccccccccccccccc, cv5, cv4] 7 (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv0, cv3, cv1, cv2, cv12, cv5, cv13, cv4] 7 Tr.E) [cv0, cv3, cv1, cv2, cv12, cv5, cv4] 8 (Tr.N Tr.E [cv0, cv3, cv1, cv2, cv12, cv5, cv4, cv15] 7 Tr.E)) [cv0, cv3, cv1, cv2, cv12, cv5, cv19] 7 (Tr.N (Tr.N Tr.E [cv0, cv3, cv1, cv2, cv12, cv13, cv4] 7 Tr.E) [cv0, cv3, cv1, cv2, cv12, cv13, cv19] 6 Tr.E)) [cv0, cv3, cv1, cv2, cv21, cv5, cv4] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv0, cv3, cv1, cv2, cv21, cv13, cv4] 6 Tr.E) [cv0, cv3, cv1, cv2, cv25, cv5, cv24, cv4] 8 Tr.E) [cv0, cv3, cv1, cv2, cv25, cv13, cv24, cv4] 7 (Tr.N (Tr.N Tr.E [cv0, cv3, cv1, cv2, cv25, 0xffffffffccccccccffffffff00000000, cv4] 7 Tr.E) [cv0, cv3, cv1, cv2, 0xffffffff000000000000000000000000, cv5, cv11, cv4] 8 Tr.E))))
def t105 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv0, cv3, cv1, cv2, cv42, cv18, cv4] 7 Tr.E) [cv0, cv3, cv1, cv2, cv42, cv18, cv15] 6 (Tr.N Tr.E [cv0, cv3, cv1, cv2, cv5, 0xffffffff333333333333333333333333, cv4] 7 Tr.E)) [cv0, cv3, cv1, cv2, cv5, 0xffffffffcccccccc0000000000000000, cv11] 7 (Tr.N (Tr.N Tr.E [cv0, cv3, cv1, cv2, cv5, cv11, cv4] 8 Tr.E) [cv0, cv3, cv1, cv2, cv5, cv11, cv15] 7 Tr.E)) [cv0, cv3, cv1, cv2, cv5, cv11, cv31] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv0, cv3, cv1, cv2, cv5, cv18, cv4] 7 Tr.E) [cv0, cv3, cv1, cv2, cv5, cv18, cv15] 6 Tr.E) [cv0, cv3, cv1, cv2, cv5, cv24, cv4, 0xffffffffffffffffcccccccccccccccc] 8 (Tr.N (Tr.N Tr.E [cv0, cv3, cv1, cv2, cv44, cv18, cv4] 6 Tr.E) [cv0, cv3, cv1, cv2, cv13, cv11, cv4] 7 Tr.E))) [cv0, cv3, cv1, cv2, cv13, cv18, cv4] 6 (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv0, cv3, cv1, cv2, 0xffffffffc8c8c8c8ffffffffc8c8c8c8, 0xffffffffffffffffc8c8c8c8c8c8c8c8] 6 Tr.E) [cv0, cv3, cv1, cv2, cv11, 0xfffffffff0f0f0f0fffffffff0f0f0f0, cv4] 7 (Tr.N Tr.E [cv0, cv3, cv1, cv2, cv11, cv27, cv4] 7 Tr.E)) [cv0, cv3, cv1, cv2, cv11, cv27, cv15] 6 (Tr.N (Tr.N Tr.E [cv0, cv3, cv1, cv2, cv11, cv27, cv31] 6 Tr.E) [cv0, cv3, cv1, cv2, cv11, 0xffffffffffaaffaaffffffffffaaffaa, cv4] 6 Tr.E)) [cv0, cv3, cv1, cv2, cv11, 0xfffffffffff0fff0fffffffffff0fff0, cv4] 6 (Tr.N (Tr.N (Tr.N Tr.E [cv0, cv3, cv1, cv2, cv11, cv4, 0xffffffffffffffffffffffff00000000] 7 Tr.E) [cv0, cv3, cv1, cv2, cv18, cv19] 6 Tr.E) [cv0, cv3, cv1, cv2, cv18, 0xffffffffffffffffffffaaaaaaaaaaaa] 5 (Tr.N (Tr.N Tr.E [cv0, cv3, cv1, cv2, 0xffffffffccccccccffffffff00000000, cv4, 0xffffffffffffffffcccccccccccccccc] 7 Tr.E) [cv0, cv3, cv1, cv52, cv21, cv5, cv4] 6 Tr.E))))
def u106 : Tr := Tr.N t104 [cv0, cv3, cv1, cv2, 0xffffffff00000000cccccccc00000000, cv11, cv4] 7 t105
def u107 : Tr := Tr.N u103 [cv0, cv3, cv1, cv28, cv2, cv5, cv11, cv4] 7 u106
def u108 : Tr := Tr.N u100 [cv0, cv29, cv3, cv2, cv5, cv27, cv4] 7 u107
def t109 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv0, cv3, cv1, cv23, cv12, cv5, cv19] 6 Tr.E) [cv0, cv3, cv1, cv23, cv25, cv5, cv24, cv4] 7 (Tr.N Tr.E [cv0, cv3, cv1, cv23, cv25, 0xffffffffccccccccffffffff00000000, cv4] 6 Tr.E)) [cv0, cv3, cv1, cv23, cv42, cv18, cv4] 6 (Tr.N (Tr.N Tr.E [cv0, cv3, cv1, cv23, cv5, cv18, cv4] 6 Tr.E) [cv0, cv3, cv1, cv23, cv18, cv19] 5 Tr.E)) [cv0, cv3, cv1, 0xffffc8c8ffc8c8c8ffffc8c8ffc8c8c8, cv5, cv4] 5 (Tr.N (Tr.N (Tr.N Tr.E [cv0, cv3, cv1, 0xffffc8c8ffffc8c8ffffc8c8ffffc8c8, 0xffffffffc8c8c8c8ffffffffc8c8c8c8, cv4] 6 Tr.E) [cv0, cv3, cv1, cv21, cv32, cv5, cv4] 6 (Tr.N Tr.E [cv0, cv3, cv1, cv21, cv5, 0xffffffffffffffffffff0000ff000000] 6 Tr.E)) [cv0, cv3, cv1, cv5, cv11, cv51, cv4] 7 (Tr.N (Tr.N Tr.E [cv0, cv3, cv1, cv5, cv11, cv51, cv15] 6 Tr.E) [cv0, cv3, cv1, cv13, cv11, cv51, cv4] 6 Tr.E))) [cv0, cv3, 0xff88ff88ff88ff88ff88ff88ff88ff88, cv2, 0xffffffffc0c0c0c0ffffffffc0c0c0c0, cv57] 5 (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv0, cv3, 0xff88ff88ff88ff88ff88ff88ff88ff88, 0xffffc0c0ffffc0c0ffffc0c0ffffc0c0, 0xffffffffc0c0c0c0ffffffffc0c0c0c0, cv4] 5 Tr.E) [cv0, cv3, 0xffc8ffc8ffc8ffc8ffc8ffc8ffc8ffc8, cv2, 0xffffffffc8c8c8c8ffffffffc8c8c8c8, 0xffffffffffffffffc8c8c8c8c8c8c8c8] 5 (Tr.N Tr.E [cv0, cv3, 0xffc8ffc8ffc8ffc8ffc8ffc8ffc8ffc8, 0xffffc8c8ffffc8c8ffffc8c8ffffc8c8, cv5, cv4] 6 Tr.E)) [cv0, cv3, 0xffc8ffc8ffc8ffc8ffc8ffc8ffc8ffc8, 0xffffc8c8ffffc8c8ffffc8c8ffffc8c8, 0xffffffffc8c8c8c8ffffffffc8c8c8c8, cv4] 5 (Tr.N (Tr.N Tr.E [cv0, cv3, cv14, cv28, cv26, cv5, cv4] 6 Tr.E) [cv0, cv3, cv14, cv28, cv2, cv5, cv4] 7 Tr.E)) [cv0, cv3, cv14, cv28, cv2, cv5, cv53] 6 (Tr.N (Tr.N (Tr.N Tr.E [cv0, cv3, cv14, cv28, cv2, cv36, cv4] 6 Tr.E) [cv0, cv3, cv14, cv28, cv5, cv4, cv35] 6 Tr.E) [cv0, cv3, cv14, cv28, cv5, cv19] 5 (Tr.N (Tr.N Tr.E [cv0, cv3, cv14, cv2, cv5, cv4, cv45] 7 Tr.E) [cv0, cv3, cv14, cv2, cv5, cv4, 0xfffffffffffffffffff0fff0fff0fff0] 6 Tr.E))))
def t110 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv0, cv3, cv14, cv50, cv5, cv4, cv45] 6 Tr.E) [cv0, cv3, 0xffcceeccffcceeccffcceeccffcceecc, cv2, cv5, 0xffffffffffffffffff00aa00ff00aa00] 6 (Tr.N Tr.E [cv0, cv3, 0xffcceeccffcceeccffcceeccffcceecc, cv2, 0xffffffffff00aa00ffffffffff00aa00, cv4] 6 Tr.E)) [cv0, cv3, 0xffccffccff00ff00ffccffccff00ff00, cv2, cv11, cv4] 6 (Tr.N (Tr.N Tr.E [cv0, cv3, 0xffccffccffccffccff00ff00ff00ff00, cv2, cv25, cv5, cv4] 7 Tr.E) [cv0, cv3, 0xffccffccffccffccff00ff00ff00ff00, cv23, cv25, cv5, cv4] 6 Tr.E)) [cv0, cv3, 0xffccffccffccffccff00ff00ff00ff00, cv25, cv50, cv5, cv4] 6 (Tr.N (Tr.N (Tr.N Tr.E [cv0, cv3, cv16, 0xffffc0c0ffc0c0c0ffffc0c0ffc0c0c0, cv5, cv4] 5 Tr.E) [cv0, cv3, cv16, 0xffffc0c0ffffc0c0ffffc0c0ffffc0c0, cv5, cv27, cv4] 6 (Tr.N Tr.E [cv0, cv3, cv16, 0xffffc0c0ffffc0c0ffffc0c0ffffc0c0, cv5, cv4, cv45] 6 Tr.E)) [cv0, cv3, cv16, 0xffffc0c0ffffc0c0ffffc0c0ffffc0c0, cv36, cv4] 5 (Tr.N (Tr.N Tr.E [cv0, cv3, cv28, cv17, cv21, cv5, cv4] 6 Tr.E) [cv0, cv3, cv28, cv17, cv11, cv4] 5 Tr.E))) [cv0, cv3, cv28, cv2, cv11, cv27, cv4] 6 (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv0, cv3, cv28, cv21, cv5, 0xffffffffffffffffffff0000ff000000] 5 Tr.E) [cv0, cv3, cv2, cv12, cv56, cv5, cv4] 7 (Tr.N Tr.E [cv0, cv3, cv2, cv12, cv56, cv13, cv4] 6 Tr.E)) [cv0, cv3, cv2, cv56, cv11, cv4] 6 (Tr.N (Tr.N Tr.E [cv0, cv3, cv2, cv56, cv11, cv15] 5 Tr.E) [cv0, cv3, cv2, cv56, cv11, cv31] 5 Tr.E)) [cv0, cv3, cv2, cv5, cv11, 0xffffffffff00ff00ff00ff00ff00ff00, cv4] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv0, cv3, cv2, cv5, cv11, 0xffffffffff00ff00ff00ff00ff00ff00, cv15] 6 Tr.E) [cv0, cv3, cv2, cv5, cv11, 0xffffffffff00ff00ff00ff00ff00ff00, cv31] 6 Tr.E) [cv0, cv3, cv2, cv13, cv11, 0xffffffffff00ff00ff00ff00ff00ff00, cv4] 6 (Tr.N (Tr.N Tr.E [cv0, cv3, cv2, cv11, 0xfffffffff0f0f0f0fffffffff0f0f0f0, 0xffffffffff00ff00ff00ff00ff00ff00, cv4] 6 Tr.E) [cv0, cv3, cv2, cv11, 0xffffffffff00ff00ffccffccff00ff00, cv4] 6 Tr.E))))
def u111 : Tr := Tr.N t109 [cv0, cv3, cv14, cv2, cv5, cv15, cv45] 6 t110
def t112 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv0, cv3, cv2, cv18, 0xffffffffff00ff00ffffff00ff00ff00, cv15] 5 Tr.E) [cv0, cv3, cv2, cv18, 0xffffffffff00ff00ffffff00ff00ff00, cv31] 5 (Tr.N Tr.E [cv0, cv3, cv23, cv12, cv56, cv5, cv4] 6 Tr.E)) [cv0, cv3, cv23, cv56, cv11, cv4] 5 (Tr.N (Tr.N Tr.E [cv0, cv3, cv23, cv18, 0xffffffffff00ff00ffffff00ff00ff00, cv4] 5 Tr.E) [cv0, cv38, cv17, cv21, cv5, cv4] 5 Tr.E)) [cv0, cv38, cv21, cv5, 0xffffffffffffffffffff0000ff000000] 4 (Tr.N (Tr.N (Tr.N Tr.E [cv0, 0xfcfcfcfcfcfcfcfcf0f0f0f0f0f0f0f0, 0xffccffccffccffccff00ff00ff00ff00, cv2, cv25, cv5, cv4] 6 Tr.E) [cv0, cv22, cv1, cv14, cv20, cv5, cv4] 6 (Tr.N Tr.E [cv0, cv22, cv1, cv12, cv20, cv5, cv4] 6 Tr.E)) [cv0, cv22, cv1, cv20, cv11, cv4] 5 (Tr.N (Tr.N Tr.E [cv0, cv22, cv1, cv18, 0xfffffffff0f0f0f0fffff0f0f0f0f0f0, cv4] 5 Tr.E) [cv0, cv40, cv12, cv20, cv5, cv4] 5 Tr.E))) [cv0, cv40, cv18, 0xfffffffff0f0f0f0fffff0f0f0f0f0f0, cv4] 4 (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv0, cv1, cv14, cv46, cv26, cv5, cv4] 6 Tr.E) [cv0, cv1, cv14, cv46, cv2, cv5, cv4] 7 (Tr.N Tr.E [cv0, cv1, cv14, cv46, cv42, cv4] 5 Tr.E)) [cv0, cv1, cv14, cv46, cv5, cv4, cv35] 6 (Tr.N (Tr.N Tr.E [cv0, cv1, cv14, cv46, cv5, cv19] 5 Tr.E) [cv0, cv1, cv14, cv20, cv5, cv4] 6 Tr.E)) [cv0, cv1, cv14, cv20, cv5, cv53] 5 (Tr.N (Tr.N (Tr.N Tr.E [cv0, cv1, cv14, cv32, cv5, cv4] 5 Tr.E) [cv0, cv1, cv16, cv25, cv20, cv5, cv4] 6 Tr.E) [cv0, cv1, cv28, cv2, cv5, cv11, cv31] 6 (Tr.N (Tr.N Tr.E [cv0, cv1, cv17, cv21, cv32, cv5, cv4] 6 Tr.E) [cv0, cv1, cv17, cv32, cv11, cv4] 5 Tr.E))))
def t113 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv0, cv1, cv17, cv11, 0xfffffffffcfcfcfcf0f0f0f0f0f0f0f0] 4 Tr.E) [cv0, cv1, cv2, cv12, cv20, cv5, cv4] 7 (Tr.N Tr.E [cv0, cv1, cv2, cv12, cv20, cv13, cv4] 6 Tr.E)) [cv0, cv1, cv2, cv20, cv11, cv4] 6 (Tr.N (Tr.N Tr.E [cv0, cv1, cv2, cv20, cv11, cv15] 5 Tr.E) [cv0, cv1, cv2, cv5, cv11, 0xfffffffff0f0f0f0f0f0f0f0f0f0f0f0, cv4] 7 Tr.E)) [cv0, cv1, cv2, cv5, cv11, 0xfffffffff0f0f0f0f0f0f0f0f0f0f0f0, cv45] 6 (Tr.N (Tr.N (Tr.N Tr.E [cv0, cv1, cv2, cv5, cv11, 0xfffffffffcfcfcfcf0f0f0f0f0f0f0f0] 6 Tr.E) [cv0, cv1, cv2, cv11, 0xfffffffff0f0f0f0f0f0f0f0f0f0f0f0, cv27, cv4] 6 Tr.E) [cv0, cv1, cv2, cv11, 0xfffffffffcfcfcfcf0f0f0f0f0f0f0f0, cv27] 5 (Tr.N (Tr.N Tr.E [cv0, cv1, cv2, cv18, 0xfffffffff0f0f0f0fffff0f0f0f0f0f0, cv4] 6 Tr.E) [cv0, cv1, cv2, cv18, 0xfffffffff0f0f0f0fffff0f0f0f0f0f0, cv15] 5 Tr.E))) [cv0, cv1, cv23, cv12, cv20, cv5, cv4] 6 (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv0, cv1, cv23, cv20, cv11, cv4] 5 Tr.E) [cv0, cv1, cv23, cv18, 0xfffffffff0f0f0f0fffff0f0f0f0f0f0, cv4] 5 (Tr.N Tr.E [cv0, cv1, cv21, cv32, 0xffffffff000000000000000000000000, cv4] 5 Tr.E)) [cv0, cv1, cv21, cv32, cv5, cv4] 6 (Tr.N (Tr.N Tr.E [cv0, cv1, cv21, cv32, cv5, 0xffffffffffffffffffff0000ff000000] 5 Tr.E) [cv0, cv1, cv21, cv32, 0xffffffffcccccccc0000000000000000] 4 Tr.E)) [cv0, cv1, cv21, cv32, cv24, cv4] 5 (Tr.N (Tr.N (Tr.N Tr.E [cv0, cv1, cv21, cv32, cv36, cv4] 5 Tr.E) [cv0, cv1, cv21, cv32, 0xffffffffffcccccc0000000000000000] 4 Tr.E) [cv0, cv1, cv21, cv32, 0xffffffffffccccccffffffffffcccccc, cv4] 5 (Tr.N (Tr.N Tr.E [cv0, cv1, cv32, 0xffffffffffccccccffffccccffcccccc, cv4] 4 Tr.E) [cv0, cv14, cv46, cv2, cv5, cv4, cv45] 6 Tr.E))))
def u114 : Tr := Tr.N t112 [cv0, cv1, cv17, cv11, 0xfffffffff0f0f0f0f0f0f0f0f0f0f0f0, cv4] 5 t113
def u115 : Tr := Tr.N u111 [cv0, cv3, cv2, cv18, 0xffffffffff00ff00ffffff00ff00ff00, cv4] 6 u114
def t116 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv0, cv14, cv28, cv5, cv31, cv35] 5 Tr.E) [cv0, 0xffcceeccffcceeccffcceeccffcceecc, 0xfff0faf0fff0faf0fff0faf0fff0faf0, cv26, cv5, cv4] 5 (Tr.N Tr.E [cv0, 0xffcceeccffcceeccffcceeccffcceecc, 0xfff0faf0fff0faf0fff0faf0fff0faf0, cv2, cv5, cv4] 6 Tr.E)) [cv0, 0xffcceeccffcceeccffcceeccffcceecc, 0xfff0faf0fff0faf0fff0faf0fff0faf0, cv42, cv4] 4 (Tr.N (Tr.N Tr.E [cv0, 0xffcceeccffcceeccffcceeccffcceecc, 0xfff0faf0fff0faf0fff0faf0fff0faf0, cv5, cv4, cv35] 5 Tr.E) [cv0, 0xffcceeccffcceeccffcceeccffcceecc, 0xfff0faf0fff0faf0fff0faf0fff0faf0, cv5, cv19] 4 Tr.E)) [cv0, cv16, cv21, cv32, cv5, cv4] 5 (Tr.N (Tr.N (Tr.N Tr.E [cv0, cv16, cv25, cv32, cv5, cv4] 5 Tr.E) [cv0, cv28, cv17, cv11, cv31] 4 (Tr.N Tr.E [cv0, cv28, cv2, cv11, cv27, cv31] 5 Tr.E)) [cv0, cv28, cv21, cv32, cv5, cv4] 5 (Tr.N (Tr.N Tr.E [cv0, cv21, cv32, cv56, cv5, cv4] 5 Tr.E) [cv0, cv21, cv32, 0xffffffccffccffccffffffccffccffcc, cv5, cv4] 5 Tr.E))) [cv0, cv21, cv32, 0xfffffff0fff0fff0fffffff0fff0fff0, cv5, cv4] 5 (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv0, cv21, 0xfffffaf0fff0faf0fffffaf0fff0faf0, cv5, cv4] 4 Tr.E) [cv0, 0xffffeeccffcceeccffffeeccffcceecc, cv32, cv5, cv4] 4 (Tr.N Tr.E [cv43, cv47, cv1, cv2, cv5, cv4] 6 Tr.E)) [cv43, cv3, 0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc, cv1, cv2, cv5, cv4] 7 (Tr.N (Tr.N Tr.E [cv43, cv3, cv1, cv16, cv2, cv5, cv4] 7 Tr.E) [cv43, cv3, cv1, cv16, cv2, 0xffffffffc0c0c0c0ffffffffc0c0c0c0, cv4] 6 Tr.E)) [cv43, cv3, 0xff88ff88ff88ff88ff88ff88ff88ff88, cv2, cv5, cv4] 6 (Tr.N (Tr.N (Tr.N Tr.E [cv43, cv3, 0xff88ff88ff88ff88ff88ff88ff88ff88, cv2, cv59, cv4] 5 Tr.E) [cv43, cv3, 0xff88ff88ff88ff88ff88ff88ff88ff88, cv2, 0xffffffffc0c0c0c0ffffffffc0c0c0c0, cv4] 5 Tr.E) [cv43, cv3, 0xffc8ffc8ffc8ffc8ffc8ffc8ffc8ffc8, cv2, cv5, cv4] 6 (Tr.N (Tr.N Tr.E [cv43, cv3, 0xffc8ffc8ffc8ffc8ffc8ffc8ffc8ffc8, cv2, 0xffffffffc8c8c8c8ffffffffc8c8c8c8, cv4] 5 Tr.E) [cv43, cv3, cv16, cv17, cv5, cv4] 5 Tr.E))))
def t117 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv43, cv3, cv16, cv2, cv36, cv4] 5 Tr.E) [cv43, 0xf8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8, cv1, cv2, cv5, cv4] 6 (Tr.N Tr.E [cv29, cv3, cv1, cv2, cv5, cv13, 0xffffffffffffffffaa00aa00aa00aa00] 6 Tr.E)) [cv29, cv3, cv1, cv55, cv5, cv13, cv4] 6 (Tr.N (Tr.N Tr.E [cv29, cv3, cv17, cv52, cv5, cv4] 5 Tr.E) [cv29, cv38, cv1, cv2, cv5, cv13, cv4] 6 Tr.E)) [cv29, cv52, cv32, cv5, cv4] 4 (Tr.N (Tr.N (Tr.N Tr.E [0xeeeceeeceeeceeeceeeceeeceeeceeec, cv41, cv1, cv2, cv5, cv4] 6 Tr.E) [0xeeeceeeceeeceeeceeeceeeceeeceeec, cv41, cv17, cv5, cv4] 4 Tr.E) [0xeeeceeeceeeceeeceeeceeeceeeceeec, cv41, cv2, cv5, cv27, cv4] 5 (Tr.N (Tr.N Tr.E [cv33, cv41, 0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc, cv1, cv2, cv5, cv4] 7 Tr.E) [cv54, cv3, cv1, cv30, cv12, cv5, cv4] 6 Tr.E))) [cv3, cv22, cv1, cv30, cv12, cv5, cv4] 6 (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv22, cv1, cv44, cv18, cv4] 5 Tr.E) [cv3, cv40, cv30, cv12, cv5, cv4] 5 (Tr.N Tr.E [cv3, cv40, cv52, cv21, cv5, cv4] 5 Tr.E)) [cv3, cv40, cv44, cv18, cv4] 4 (Tr.N (Tr.N Tr.E [cv3, 0xff00ff0000000000ff00ff0000000000, cv1, cv2, cv30, cv12, cv4] 6 Tr.E) [cv3, 0xff00ff00ff00aa00ff00aa00ff00aa00, cv44, cv18, cv4] 4 Tr.E)) [cv3, cv1, cv39, cv14, cv26, cv5, cv4] 6 (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv1, cv39, cv14, cv2, cv5, cv4] 7 Tr.E) [cv3, cv1, cv39, cv14, cv42, cv4] 5 Tr.E) [cv3, cv1, cv39, cv14, cv5, cv4, cv35] 6 (Tr.N (Tr.N Tr.E [cv3, cv1, cv39, cv14, cv5, cv19] 5 Tr.E) [cv3, cv1, cv39, cv26, cv12, cv5, cv4] 6 Tr.E))))
def u118 : Tr := Tr.N t116 [cv43, cv3, cv16, cv2, cv5, cv27, cv4] 6 t117
def t119 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv1, cv39, cv12, cv5, cv19] 5 Tr.E) [cv3, cv1, cv39, cv25, cv5, cv24, cv4] 6 (Tr.N Tr.E [cv3, cv1, cv39, cv25, 0xffffffffccccccccffffffff00000000, cv4] 5 Tr.E)) [cv3, cv1, cv39, cv42, cv18, cv4] 5 (Tr.N (Tr.N Tr.E [cv3, cv1, cv39, cv18, cv19] 4 Tr.E) [cv3, cv1, cv14, cv26, cv30, cv5, cv4] 6 Tr.E)) [cv3, cv1, cv14, cv30, cv5, cv19] 5 (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv1, cv16, cv30, cv25, cv5, cv4] 6 Tr.E) [cv3, cv1, cv26, cv2, cv30, cv12, cv5, cv4] 7 (Tr.N Tr.E [cv3, cv1, cv26, cv2, cv11, 0xffffffffeeeeeeeeaaaaaaaaaaaaaaaa] 5 Tr.E)) [cv3, cv1, cv17, cv52, cv21, cv5, cv4] 6 (Tr.N (Tr.N Tr.E [cv3, cv1, cv17, cv11, 0xffffffffeeeeeeeeaaaaaaaaaaaaaaaa] 4 Tr.E) [cv3, cv1, cv2, cv30, cv12, cv5, cv4] 7 Tr.E))) [cv3, cv1, cv2, cv30, cv12, cv5, cv19] 6 (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv1, cv2, cv30, cv12, cv13, cv4] 6 Tr.E) [cv3, cv1, cv2, cv30, cv12, cv24, cv4] 6 (Tr.N Tr.E [cv3, cv1, cv2, cv30, cv12, 0xffffffffffff0000ffffffffffff0000, cv4] 6 Tr.E)) [cv3, cv1, cv2, cv30, cv25, cv24, cv4] 6 (Tr.N (Tr.N Tr.E [cv3, cv1, cv2, cv30, cv18, cv4] 5 Tr.E) [cv3, cv1, cv2, cv23, cv12, cv13, cv4] 6 Tr.E)) [cv3, cv1, cv2, cv12, 0xffffffffaaaaaaaaaaaaaaaaaaaaaaaa, cv19] 5 (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv1, cv2, cv12, cv44, cv4] 5 Tr.E) [cv3, cv1, cv2, cv12, cv13, 0xffffffffffffffffaa00aa00aa00aa00] 5 Tr.E) [cv3, cv1, cv2, cv5, 0xffffffffaaaaaaaaaaaaaaaaaaaaaaaa, cv11, cv45] 6 (Tr.N (Tr.N Tr.E [cv3, cv1, cv2, cv5, cv11, 0xffffffffeeeeeeeeaaaaaaaaaaaaaaaa] 6 Tr.E) [cv3, cv1, cv2, cv44, cv18, cv4] 6 Tr.E))))
def t120 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv1, cv2, cv44, cv18, cv31] 5 Tr.E) [cv3, cv1, cv2, cv44, cv18, cv19] 5 (Tr.N Tr.E [cv3, cv1, cv2, cv44, cv18, 0xffffffffffffffffffffaaaaaaaaaaaa] 5 Tr.E)) [cv3, cv1, cv2, cv13, cv11, 0xffffffffffffffffaa00aa00aa00aa00] 5 (Tr.N (Tr.N Tr.E [cv3, cv1, cv2, cv13, cv18, cv15] 5 Tr.E) [cv3, cv1, cv2, cv11, 0xffffffffeeeeeeeeaaaaaaaaaaaaaaaa, cv27] 5 Tr.E)) [cv3, cv1, cv2, cv18, 0xffffffffeeeeeeeeffffaaaaaaaaaaaa] 4 (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv1, cv55, cv12, cv13, cv4] 5 Tr.E) [cv3, cv1, cv52, cv21, cv5, 0xffffffffffffffffffff0000ff000000] 5 Tr.E) [cv3, cv1, cv52, cv21, cv24, cv4] 5 (Tr.N (Tr.N Tr.E [cv3, cv1, cv52, cv21, cv36, cv4] 5 Tr.E) [cv3, cv1, cv52, cv21, 0xffffffffffccccccffffffffffcccccc, cv4] 5 Tr.E))) [cv3, cv1, cv52, cv25, cv24, cv4] 5 (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv1, cv52, 0xffffffffffccccccffffccccffcccccc, cv4] 4 Tr.E) [cv3, cv1, cv23, cv25, cv13, cv24, cv4] 6 (Tr.N Tr.E [cv3, cv39, 0xffcceeccffcceeccffcceeccffcceecc, cv5, cv19] 4 Tr.E)) [cv38, cv52, cv21, cv5, cv4] 4 (Tr.N (Tr.N Tr.E [cv1, cv39, cv14, cv20, cv5, cv4] 5 Tr.E) [cv1, cv39, cv12, cv20, cv5, cv4] 5 Tr.E)) [cv1, cv39, cv20, cv11, cv4] 4 (Tr.N (Tr.N (Tr.N Tr.E [cv1, cv39, cv18, 0xfffffffff0f0f0f0fffff0f0f0f0f0f0, cv4] 4 Tr.E) [cv1, cv14, cv30, cv20, cv5, cv4] 5 Tr.E) [cv1, cv2, cv30, cv12, cv20, cv5, cv4] 6 (Tr.N (Tr.N Tr.E [cv1, cv2, cv44, cv18, 0xfffffffff0f0f0f0fffff0f0f0f0f0f0, cv4] 5 Tr.E) [cv1, cv2, cv44, cv18, 0xfffffffffcfcfcfcf0f0f0f0f0f0f0f0] 4 Tr.E))))
def u121 : Tr := Tr.N t119 [cv3, cv1, cv2, cv44, cv18, cv15] 5 t120
def u122 : Tr := Tr.N u118 [cv3, cv1, cv39, cv12, cv5, cv4] 6 u121
def u123 : Tr := Tr.N u115 [cv0, cv14, cv28, cv2, cv5, cv4, cv31] 6 u122
def u124 : Tr := Tr.N u108 [cv0, cv3, cv1, cv23, cv12, cv5, cv4] 7 u123
def u125 : Tr := Tr.N u93 [cv0, cv6, 0xfaf0f0f0faf0f0f0faf0f0f0faf0f0f0, cv1, cv2, cv5, cv4] 7 u124
def tree : Tr := Tr.N u62 [cv0, cv6, cv3, cv3, cv1, cv2, cv5, cv4] 9 u125

theorem allE_N (t l r : Tr) (k : List ℕ) (v : ℕ) :
    allE t (Tr.N l k v r) = (chkE t k v && allE t l && allE t r) := rfl

theorem allE_E (t : Tr) : allE t Tr.E = true := rfl

set_option maxHeartbeats 400000000 in
theorem ok_t0 : allE tree t0 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t1 : allE tree t1 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u2 : allE tree u2 = true := by
  unfold u2
  rw [allE_N, ok_t0, ok_t1, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t3 : allE tree t3 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t4 : allE tree t4 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u5 : allE tree u5 = true := by
  unfold u5
  rw [allE_N, ok_t3, ok_t4, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u6 : allE tree u6 = true := by
  unfold u6
  rw [allE_N, ok_u2, ok_u5, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t7 : allE tree t7 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t8 : allE tree t8 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u9 : allE tree u9 = true := by
  unfold u9
  rw [allE_N, ok_t7, ok_t8, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t10 : allE tree t10 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t11 : allE tree t11 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u12 : allE tree u12 = true := by
  unfold u12
  rw [allE_N, ok_t10, ok_t11, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u13 : allE tree u13 = true := by
  unfold u13
  rw [allE_N, ok_u9, ok_u12, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u14 : allE tree u14 = true := by
  unfold u14
  rw [allE_N, ok_u6, ok_u13, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t15 : allE tree t15 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t16 : allE tree t16 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u17 : allE tree u17 = true := by
  unfold u17
  rw [allE_N, ok_t15, ok_t16, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t18 : allE tree t18 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t19 : allE tree t19 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u20 : allE tree u20 = true := by
  unfold u20
  rw [allE_N, ok_t18, ok_t19, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u21 : allE tree u21 = true := by
  unfold u21
  rw [allE_N, ok_u17, ok_u20, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t22 : allE tree t22 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t23 : allE tree t23 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u24 : allE tree u24 = true := by
  unfold u24
  rw [allE_N, ok_t22, ok_t23, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t25 : allE tree t25 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t26 : allE tree t26 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u27 : allE tree u27 = true := by
  unfold u27
  rw [allE_N, ok_t25, ok_t26, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u28 : allE tree u28 = true := by
  unfold u28
  rw [allE_N, ok_u24, ok_u27, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u29 : allE tree u29 = true := by
  unfold u29
  rw [allE_N, ok_u21, ok_u28, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u30 : allE tree u30 = true := by
  unfold u30
  rw [allE_N, ok_u14, ok_u29, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t31 : allE tree t31 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t32 : allE tree t32 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u33 : allE tree u33 = true := by
  unfold u33
  rw [allE_N, ok_t31, ok_t32, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t34 : allE tree t34 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t35 : allE tree t35 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u36 : allE tree u36 = true := by
  unfold u36
  rw [allE_N, ok_t34, ok_t35, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u37 : allE tree u37 = true := by
  unfold u37
  rw [allE_N, ok_u33, ok_u36, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t38 : allE tree t38 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t39 : allE tree t39 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u40 : allE tree u40 = true := by
  unfold u40
  rw [allE_N, ok_t38, ok_t39, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t41 : allE tree t41 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t42 : allE tree t42 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u43 : allE tree u43 = true := by
  unfold u43
  rw [allE_N, ok_t41, ok_t42, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u44 : allE tree u44 = true := by
  unfold u44
  rw [allE_N, ok_u40, ok_u43, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u45 : allE tree u45 = true := by
  unfold u45
  rw [allE_N, ok_u37, ok_u44, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t46 : allE tree t46 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t47 : allE tree t47 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u48 : allE tree u48 = true := by
  unfold u48
  rw [allE_N, ok_t46, ok_t47, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t49 : allE tree t49 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t50 : allE tree t50 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u51 : allE tree u51 = true := by
  unfold u51
  rw [allE_N, ok_t49, ok_t50, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u52 : allE tree u52 = true := by
  unfold u52
  rw [allE_N, ok_u48, ok_u51, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t53 : allE tree t53 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t54 : allE tree t54 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u55 : allE tree u55 = true := by
  unfold u55
  rw [allE_N, ok_t53, ok_t54, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t56 : allE tree t56 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t57 : allE tree t57 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u58 : allE tree u58 = true := by
  unfold u58
  rw [allE_N, ok_t56, ok_t57, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u59 : allE tree u59 = true := by
  unfold u59
  rw [allE_N, ok_u55, ok_u58, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u60 : allE tree u60 = true := by
  unfold u60
  rw [allE_N, ok_u52, ok_u59, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u61 : allE tree u61 = true := by
  unfold u61
  rw [allE_N, ok_u45, ok_u60, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u62 : allE tree u62 = true := by
  unfold u62
  rw [allE_N, ok_u30, ok_u61, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t63 : allE tree t63 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t64 : allE tree t64 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u65 : allE tree u65 = true := by
  unfold u65
  rw [allE_N, ok_t63, ok_t64, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t66 : allE tree t66 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t67 : allE tree t67 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u68 : allE tree u68 = true := by
  unfold u68
  rw [allE_N, ok_t66, ok_t67, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u69 : allE tree u69 = true := by
  unfold u69
  rw [allE_N, ok_u65, ok_u68, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t70 : allE tree t70 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t71 : allE tree t71 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u72 : allE tree u72 = true := by
  unfold u72
  rw [allE_N, ok_t70, ok_t71, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t73 : allE tree t73 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t74 : allE tree t74 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u75 : allE tree u75 = true := by
  unfold u75
  rw [allE_N, ok_t73, ok_t74, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u76 : allE tree u76 = true := by
  unfold u76
  rw [allE_N, ok_u72, ok_u75, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u77 : allE tree u77 = true := by
  unfold u77
  rw [allE_N, ok_u69, ok_u76, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t78 : allE tree t78 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t79 : allE tree t79 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u80 : allE tree u80 = true := by
  unfold u80
  rw [allE_N, ok_t78, ok_t79, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t81 : allE tree t81 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t82 : allE tree t82 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u83 : allE tree u83 = true := by
  unfold u83
  rw [allE_N, ok_t81, ok_t82, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u84 : allE tree u84 = true := by
  unfold u84
  rw [allE_N, ok_u80, ok_u83, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t85 : allE tree t85 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t86 : allE tree t86 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u87 : allE tree u87 = true := by
  unfold u87
  rw [allE_N, ok_t85, ok_t86, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t88 : allE tree t88 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t89 : allE tree t89 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u90 : allE tree u90 = true := by
  unfold u90
  rw [allE_N, ok_t88, ok_t89, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u91 : allE tree u91 = true := by
  unfold u91
  rw [allE_N, ok_u87, ok_u90, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u92 : allE tree u92 = true := by
  unfold u92
  rw [allE_N, ok_u84, ok_u91, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u93 : allE tree u93 = true := by
  unfold u93
  rw [allE_N, ok_u77, ok_u92, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t94 : allE tree t94 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t95 : allE tree t95 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u96 : allE tree u96 = true := by
  unfold u96
  rw [allE_N, ok_t94, ok_t95, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t97 : allE tree t97 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t98 : allE tree t98 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u99 : allE tree u99 = true := by
  unfold u99
  rw [allE_N, ok_t97, ok_t98, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u100 : allE tree u100 = true := by
  unfold u100
  rw [allE_N, ok_u96, ok_u99, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t101 : allE tree t101 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t102 : allE tree t102 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u103 : allE tree u103 = true := by
  unfold u103
  rw [allE_N, ok_t101, ok_t102, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t104 : allE tree t104 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t105 : allE tree t105 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u106 : allE tree u106 = true := by
  unfold u106
  rw [allE_N, ok_t104, ok_t105, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u107 : allE tree u107 = true := by
  unfold u107
  rw [allE_N, ok_u103, ok_u106, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u108 : allE tree u108 = true := by
  unfold u108
  rw [allE_N, ok_u100, ok_u107, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t109 : allE tree t109 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t110 : allE tree t110 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u111 : allE tree u111 = true := by
  unfold u111
  rw [allE_N, ok_t109, ok_t110, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t112 : allE tree t112 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t113 : allE tree t113 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u114 : allE tree u114 = true := by
  unfold u114
  rw [allE_N, ok_t112, ok_t113, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u115 : allE tree u115 = true := by
  unfold u115
  rw [allE_N, ok_u111, ok_u114, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t116 : allE tree t116 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t117 : allE tree t117 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u118 : allE tree u118 = true := by
  unfold u118
  rw [allE_N, ok_t116, ok_t117, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t119 : allE tree t119 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t120 : allE tree t120 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u121 : allE tree u121 = true := by
  unfold u121
  rw [allE_N, ok_t119, ok_t120, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u122 : allE tree u122 = true := by
  unfold u122
  rw [allE_N, ok_u118, ok_u121, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u123 : allE tree u123 = true := by
  unfold u123
  rw [allE_N, ok_u115, ok_u122, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u124 : allE tree u124 = true := by
  unfold u124
  rw [allE_N, ok_u108, ok_u123, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u125 : allE tree u125 = true := by
  unfold u125
  rw [allE_N, ok_u93, ok_u124, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_tree : allE tree tree = true := by
  have h : allE tree (Tr.N u62 [cv0, cv6, cv3, cv3, cv1, cv2, cv5, cv4] 9 u125) = true := by
    rw [allE_N, ok_u62, ok_u125, Bool.and_true, Bool.and_true]
    decide +kernel
  exact h


set_option maxHeartbeats 400000000 in
theorem top_ok : ∀ L ∈ XX.sublists, passes 10 L = true → lookS tree 10 L = true := by
  decide +kernel

set_option maxHeartbeats 40000000 in
theorem TT_eq : encL fE pts = TT := by decide +kernel

set_option maxHeartbeats 40000000 in
theorem AA_eq' : encL (fun _ => true) pts = AA := by decide +kernel

set_option maxHeartbeats 40000000 in
theorem XX_eq : (List.range 7).map (Xv pts) = XX := by decide +kernel

theorem Run.mono_le {s s' : ℕ} {L : List ℕ} (hs : s ≤ s') (h : Run TT AA s L) : Run TT AA s' L := by
  induction hs with
  | refl => exact h
  | step _ ih => exact Run.mono ih

theorem main : ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ (∀ x : Fin 7 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 7, (u.val, v.val) ∈ ([(0, 1), (0, 2), (2, 1), (0, 3), (3, 4), (4, 5), (5, 6), (6, 1)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true))) := by
  rintro ⟨C, hF, hsize, hf⟩
  have hsz : C.gates.length ≤ 10 := hsize
  have hf' : ∀ x, C.eval (List.ofFn x) = fE x := fun x =>
    Bool.eq_iff_iff.2 ((hf x).trans decide_eq_true_iff.symm)
  have hx0 : fE (fun i => decide (i.val = 0 ∨ i.val = 1)) = true := by decide
  obtain ⟨S, hsub, hrun⟩ := reduce pts fE _ hx0 C hF hf'
  rw [TT_eq, AA_eq'] at hrun
  rw [XX_eq] at hsub
  have hr10 : Run TT AA 10 S := Run.mono_le hsz hrun
  have hl := top_ok S (List.mem_sublists.2 hsub) (hr10.passOk (le_refl 10))
  obtain ⟨g, hg, v, hm, hv⟩ := lookS_sound hl
  exact cert tree ok_tree hr10 g hg v hm hv

end PEqualNP.Outside.L_meta_595

theorem PEqualNP.Outside.L_meta_595 : ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ (∀ x : Fin 7 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 7, (u.val, v.val) ∈ ([(0, 1), (0, 2), (2, 1), (0, 3), (3, 4), (4, 5), (5, 6), (6, 1)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true))) :=
  PEqualNP.Outside.L_meta_595.main
