import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_185

open PEqualNP.MetaComplexity

def upd {n : ℕ} (x : Fin n → Bool) (i : Fin n) (c : Bool) : Fin n → Bool :=
  fun k => if k = i then c else x k

def occ {n : ℕ} : DMFormula n → Fin n → ℕ
  | .lit i _ => fun k => if k = i then 1 else 0
  | .and a b => fun k => occ a k + occ b k
  | .or a b => fun k => occ a k + occ b k

theorem eval_congr (φ : DMFormula 5) (x y : Fin 5 → Bool)
    (h : ∀ k, 1 ≤ occ φ k → x k = y k) : φ.eval x = φ.eval y := by
  induction φ with
  | lit i b =>
    simp only [DMFormula.eval]
    rw [h i (by simp [occ])]
  | and a b iha ihb =>
    simp only [DMFormula.eval]
    rw [iha (fun k hk => h k (by simp [occ]; omega)),
      ihb (fun k hk => h k (by simp [occ]; omega))]
  | or a b iha ihb =>
    simp only [DMFormula.eval]
    rw [iha (fun k hk => h k (by simp [occ]; omega)),
      ihb (fun k hk => h k (by simp [occ]; omega))]

theorem eval_upd_zero (φ : DMFormula 5) (i : Fin 5) (h : occ φ i = 0)
    (x : Fin 5 → Bool) (c : Bool) : φ.eval (upd x i c) = φ.eval x := by
  apply eval_congr
  intro k hk
  have hki : k ≠ i := by
    intro e
    subst e
    omega
  simp [upd, hki]

abbrev RForm (n : ℕ) := Bool × Option (DMFormula n)

def rEval (r : RForm n) (x : Fin n → Bool) : Bool :=
  match r.2 with
  | none => r.1
  | some φ => φ.eval x

def rSize (r : RForm n) : ℕ := (r.2.map DMFormula.leaves).getD 0

theorem rSize_some (φ : DMFormula n) : rSize (false, some φ) = φ.leaves := rfl

def rAnd (p q : RForm n) : RForm n :=
  match p.2, q.2 with
  | some a, some b => (false, some (.and a b))
  | none, some _ => if p.1 then q else (false, none)
  | some _, none => if q.1 then p else (false, none)
  | none, none => (p.1 && q.1, none)

def rOr (p q : RForm n) : RForm n :=
  match p.2, q.2 with
  | some a, some b => (false, some (.or a b))
  | none, some _ => if p.1 then (true, none) else q
  | some _, none => if q.1 then (true, none) else p
  | none, none => (p.1 || q.1, none)

theorem rAnd_eval (p q : RForm n) (x : Fin n → Bool) :
    rEval (rAnd p q) x = (rEval p x && rEval q x) := by
  cases p with
  | mk pc po =>
    cases q with
    | mk qc qo =>
      cases po with
      | none =>
        cases qo with
        | none => simp [rAnd, rEval]
        | some b => cases pc <;> simp [rAnd, rEval]
      | some a =>
        cases qo with
        | none => cases qc <;> simp [rAnd, rEval]
        | some b => simp [rAnd, rEval, DMFormula.eval]

theorem rOr_eval (p q : RForm n) (x : Fin n → Bool) :
    rEval (rOr p q) x = (rEval p x || rEval q x) := by
  cases p with
  | mk pc po =>
    cases q with
    | mk qc qo =>
      cases po with
      | none =>
        cases qo with
        | none => simp [rOr, rEval]
        | some b => cases pc <;> simp [rOr, rEval]
      | some a =>
        cases qo with
        | none => cases qc <;> simp [rOr, rEval]
        | some b => simp [rOr, rEval, DMFormula.eval]

def restrictR : DMFormula n → Fin n → Bool → RForm n
  | .lit j b, i, c => if j = i then (if b then c else !c, none) else (false, some (.lit j b))
  | .and a b, i, c => rAnd (restrictR a i c) (restrictR b i c)
  | .or a b, i, c => rOr (restrictR a i c) (restrictR b i c)

theorem restrictR_eval (φ : DMFormula n) (i : Fin n) (c : Bool) (x : Fin n → Bool) :
    rEval (restrictR φ i c) x = φ.eval (upd x i c) := by
  induction φ with
  | lit j b =>
    by_cases h : j = i
    · subst h
      simp [restrictR, rEval, upd, DMFormula.eval]
    · simp [restrictR, rEval, h, upd, DMFormula.eval]
  | and a b iha ihb =>
    change rEval (rAnd (restrictR a i c) (restrictR b i c)) x = _
    rw [rAnd_eval, iha, ihb]
    rfl
  | or a b iha ihb =>
    change rEval (rOr (restrictR a i c) (restrictR b i c)) x = _
    rw [rOr_eval, iha, ihb]
    rfl

theorem rAnd_size (p q : RForm n) : rSize (rAnd p q) ≤ rSize p + rSize q := by
  cases p with
  | mk pc po =>
    cases q with
    | mk qc qo =>
      cases po with
      | none =>
        cases qo with
        | none => simp [rAnd, rSize]
        | some b => cases pc <;> simp [rAnd, rSize]
      | some a =>
        cases qo with
        | none => cases qc <;> simp [rAnd, rSize]
        | some b => simp [rAnd, rSize, DMFormula.leaves]

theorem rOr_size (p q : RForm n) : rSize (rOr p q) ≤ rSize p + rSize q := by
  cases p with
  | mk pc po =>
    cases q with
    | mk qc qo =>
      cases po with
      | none =>
        cases qo with
        | none => simp [rOr, rSize]
        | some b => cases pc <;> simp [rOr, rSize]
      | some a =>
        cases qo with
        | none => cases qc <;> simp [rOr, rSize]
        | some b => simp [rOr, rSize, DMFormula.leaves]

theorem occ_le_leaves {n : ℕ} (φ : DMFormula n) (i : Fin n) : occ φ i ≤ φ.leaves := by
  induction φ with
  | lit j b =>
    by_cases h : j = i
    · subst j
      simp [occ, DMFormula.leaves]
    · have h' : i ≠ j := Ne.symm h
      simp [occ, DMFormula.leaves, h']
  | and a b iha ihb => simp [occ, DMFormula.leaves]; omega
  | or a b iha ihb => simp [occ, DMFormula.leaves]; omega

theorem leaves_pos {n : ℕ} (φ : DMFormula n) : 1 ≤ φ.leaves := by
  induction φ with
  | lit => simp [DMFormula.leaves]
  | and a b iha ihb => simp [DMFormula.leaves]; omega
  | or a b iha ihb => simp [DMFormula.leaves]; omega

theorem restrictR_size {n : ℕ} (φ : DMFormula n) (i : Fin n) (c : Bool) :
    rSize (restrictR φ i c) ≤ φ.leaves - occ φ i := by
  induction φ with
  | lit j b =>
    by_cases h : j = i
    · subst j
      simp [restrictR, rSize, occ, DMFormula.leaves]
    · have h' : i ≠ j := Ne.symm h
      simp [restrictR, rSize, occ, DMFormula.leaves, h, h']
  | and a b iha ihb =>
    have ha := occ_le_leaves a i
    have hb := occ_le_leaves b i
    calc
      rSize (restrictR (.and a b) i c) ≤ rSize (restrictR a i c) + rSize (restrictR b i c) := by
        exact rAnd_size _ _
      _ ≤ (a.leaves - occ a i) + (b.leaves - occ b i) := Nat.add_le_add iha ihb
      _ = (a.leaves + b.leaves) - (occ a i + occ b i) := by omega
  | or a b iha ihb =>
    have ha := occ_le_leaves a i
    have hb := occ_le_leaves b i
    calc
      rSize (restrictR (.or a b) i c) ≤ rSize (restrictR a i c) + rSize (restrictR b i c) := by
        exact rOr_size _ _
      _ ≤ (a.leaves - occ a i) + (b.leaves - occ b i) := Nat.add_le_add iha ihb
      _ = (a.leaves + b.leaves) - (occ a i + occ b i) := by omega

theorem restrictR_zero {n : ℕ} (φ : DMFormula n) (i : Fin n) (c : Bool) (h : occ φ i = 0) :
    restrictR φ i c = (false, some φ) := by
  revert h
  induction φ with
  | lit j b =>
    intro h
    have hji : j ≠ i := by
      intro e
      subst e
      simp [occ] at h
    simp [restrictR, hji]
  | and a b iha ihb =>
    intro h
    have ha : occ a i = 0 := by simp [occ] at h; omega
    have hb : occ b i = 0 := by simp [occ] at h; omega
    simp [restrictR, iha ha, ihb hb, rAnd]
  | or a b iha ihb =>
    intro h
    have ha : occ a i = 0 := by simp [occ] at h; omega
    have hb : occ b i = 0 := by simp [occ] at h; omega
    simp [restrictR, iha ha, ihb hb, rOr]

theorem occ_one_nonlit_two {n : ℕ} (φ : DMFormula n) (i : Fin n)
    (h : occ φ i = 1) (hn : ∀ s, φ ≠ .lit i s) : 2 ≤ φ.leaves := by
  cases φ with
  | lit j b =>
      by_cases hji : j = i
      · subst j
        exact (hn b rfl).elim
      · simp [occ] at h
        omega
  | and a b => have ha := leaves_pos a; have hb := leaves_pos b; simp [DMFormula.leaves]; omega
  | or a b => have ha := leaves_pos a; have hb := leaves_pos b; simp [DMFormula.leaves]; omega

theorem single_pair_size (φ : DMFormula 5) (i : Fin 5) (hocc : occ φ i = 1)
    (hn : ∀ s, φ ≠ .lit i s) :
    rSize (restrictR φ i false) + rSize (restrictR φ i true) + 3 ≤ 2 * φ.leaves := by
  induction φ with
  | lit j b =>
      have hji : j = i := by
        by_contra hji
        simp [occ, Ne.symm hji] at hocc
      subst j
      exact (hn b rfl).elim
  | and a b iha ihb =>
      simp only [restrictR]
      have hs : occ a i + occ b i = 1 := by simpa [occ] using hocc
      by_cases ha : occ a i = 1
      · have hb : occ b i = 0 := by omega
        by_cases hleaf : ∃ s, a = .lit i s
        · obtain ⟨s, rfl⟩ := hleaf
          rw [restrictR_zero b i false hb, restrictR_zero b i true hb]
          have hbpos := leaves_pos b
          cases s <;> simp [restrictR, rAnd, rSize, DMFormula.leaves] <;> omega
        · have hna' : ∀ s, a ≠ .lit i s := by
            intro s hs
            exact hleaf ⟨s, hs⟩
          have ih := iha ha hna'
          have h0 := rAnd_size (restrictR a i false) (restrictR b i false)
          have h1 := rAnd_size (restrictR a i true) (restrictR b i true)
          rw [restrictR_zero b i false hb] at h0
          rw [restrictR_zero b i true hb] at h1
          rw [restrictR_zero b i false hb, restrictR_zero b i true hb]
          have hbs : rSize (false, some b) = b.leaves := by simp [rSize]
          rw [hbs] at h0 h1
          have hsum := Nat.add_le_add h0 h1
          simp only [DMFormula.leaves] at ih ⊢
          have hap := leaves_pos a
          have hbp := leaves_pos b
          have ha2 := occ_one_nonlit_two a i ha hna'
          omega
      · have ha0 : occ a i = 0 := by omega
        have hb : occ b i = 1 := by omega
        by_cases hleaf : ∃ s, b = .lit i s
        · obtain ⟨s, rfl⟩ := hleaf
          rw [restrictR_zero a i false ha0, restrictR_zero a i true ha0]
          have hapos := leaves_pos a
          cases s <;> simp [restrictR, rAnd, rSize, DMFormula.leaves] <;> omega
        · have hnb' : ∀ s, b ≠ .lit i s := by
            intro s hs
            exact hleaf ⟨s, hs⟩
          have ih := ihb hb hnb'
          have h0 := rAnd_size (restrictR a i false) (restrictR b i false)
          have h1 := rAnd_size (restrictR a i true) (restrictR b i true)
          rw [restrictR_zero a i false ha0] at h0
          rw [restrictR_zero a i true ha0] at h1
          rw [restrictR_zero a i false ha0, restrictR_zero a i true ha0]
          have has : rSize (false, some a) = a.leaves := by simp [rSize]
          rw [has] at h0 h1
          have hsum := Nat.add_le_add h0 h1
          simp only [DMFormula.leaves] at ih ⊢
          have hap := leaves_pos a
          have hbp := leaves_pos b
          have hb2 := occ_one_nonlit_two b i hb hnb'
          omega
  | or a b iha ihb =>
      simp only [restrictR]
      have hs : occ a i + occ b i = 1 := by simpa [occ] using hocc
      by_cases ha : occ a i = 1
      · have hb : occ b i = 0 := by omega
        by_cases hleaf : ∃ s, a = .lit i s
        · obtain ⟨s, rfl⟩ := hleaf
          rw [restrictR_zero b i false hb, restrictR_zero b i true hb]
          have hbpos := leaves_pos b
          cases s <;> simp [restrictR, rOr, rSize, DMFormula.leaves] <;> omega
        · have hna' : ∀ s, a ≠ .lit i s := by
            intro s hs
            exact hleaf ⟨s, hs⟩
          have ih := iha ha hna'
          have h0 := rOr_size (restrictR a i false) (restrictR b i false)
          have h1 := rOr_size (restrictR a i true) (restrictR b i true)
          rw [restrictR_zero b i false hb] at h0
          rw [restrictR_zero b i true hb] at h1
          rw [restrictR_zero b i false hb, restrictR_zero b i true hb]
          have hbs : rSize (false, some b) = b.leaves := by simp [rSize]
          rw [hbs] at h0 h1
          have hsum := Nat.add_le_add h0 h1
          simp only [DMFormula.leaves] at ih ⊢
          have hap := leaves_pos a
          have hbp := leaves_pos b
          have ha2 := occ_one_nonlit_two a i ha hna'
          omega
      · have ha0 : occ a i = 0 := by omega
        have hb : occ b i = 1 := by omega
        by_cases hleaf : ∃ s, b = .lit i s
        · obtain ⟨s, rfl⟩ := hleaf
          rw [restrictR_zero a i false ha0, restrictR_zero a i true ha0]
          have hapos := leaves_pos a
          cases s <;> simp [restrictR, rOr, rSize, DMFormula.leaves] <;> omega
        · have hnb' : ∀ s, b ≠ .lit i s := by
            intro s hs
            exact hleaf ⟨s, hs⟩
          have ih := ihb hb hnb'
          have h0 := rOr_size (restrictR a i false) (restrictR b i false)
          have h1 := rOr_size (restrictR a i true) (restrictR b i true)
          rw [restrictR_zero a i false ha0] at h0
          rw [restrictR_zero a i true ha0] at h1
          rw [restrictR_zero a i false ha0, restrictR_zero a i true ha0]
          have has : rSize (false, some a) = a.leaves := by simp [rSize]
          rw [has] at h0 h1
          have hsum := Nat.add_le_add h0 h1
          simp only [DMFormula.leaves] at ih ⊢
          have hap := leaves_pos a
          have hbp := leaves_pos b
          have hb2 := occ_one_nonlit_two b i hb hnb'
          omega

theorem once_case_impossible (φ : DMFormula 5) (hle : φ.leaves ≤ 7)
    (hocc : occ φ 4 = 1) (hn : ∀ s, φ ≠ .lit 4 s)
    (h0 : 6 ≤ rSize (restrictR φ 4 false))
    (h1 : 6 ≤ rSize (restrictR φ 4 true)) : False := by
  have hp := single_pair_size φ 4 hocc hn
  have hpos := leaves_pos φ
  omega


abbrev T3 := Fin 3 → Bool
abbrev RowTable := Bool × Bool × Bool × Bool × Bool × Bool × Bool × Bool

def rowInput (r : Fin 8) : T3 := fun i => decide (r.val / 2 ^ i.val % 2 = 1)

def majority3 (x : T3) : Bool :=
  (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2)

def rowTable (f : Fin 8 → Bool) : RowTable := (f 0, f 1, f 2, f 3, f 4, f 5, f 6, f 7)

def litTable (i : Fin 3) (positive : Bool) : RowTable :=
  rowTable (fun r => if positive then rowInput r i else !(rowInput r i))

def literalTables : List RowTable :=
  [litTable 0 true, litTable 0 false,
   litTable 1 true, litTable 1 false,
   litTable 2 true, litTable 2 false]

def andTable (a b : RowTable) : RowTable :=
  (a.1 && b.1, a.2.1 && b.2.1, a.2.2.1 && b.2.2.1, a.2.2.2.1 && b.2.2.2.1,
   a.2.2.2.2.1 && b.2.2.2.2.1, a.2.2.2.2.2.1 && b.2.2.2.2.2.1,
   a.2.2.2.2.2.2.1 && b.2.2.2.2.2.2.1, a.2.2.2.2.2.2.2 && b.2.2.2.2.2.2.2)
def orTable (a b : RowTable) : RowTable :=
  (a.1 || b.1, a.2.1 || b.2.1, a.2.2.1 || b.2.2.1, a.2.2.2.1 || b.2.2.2.1,
   a.2.2.2.2.1 || b.2.2.2.2.1, a.2.2.2.2.2.1 || b.2.2.2.2.2.1,
   a.2.2.2.2.2.2.1 || b.2.2.2.2.2.2.1, a.2.2.2.2.2.2.2 || b.2.2.2.2.2.2.2)

theorem rowTable_and (f g : Fin 8 → Bool) :
    rowTable (fun r => f r && g r) = andTable (rowTable f) (rowTable g) := by
  rfl
theorem rowTable_or (f g : Fin 8 → Bool) :
    rowTable (fun r => f r || g r) = orTable (rowTable f) (rowTable g) := by
  rfl

theorem rowTable_congr {f g : Fin 8 → Bool} (h : ∀ r, f r = g r) :
    rowTable f = rowTable g := by
  simp [rowTable, h]

def pairTables (xs ys : List RowTable) : List RowTable :=
  xs.flatMap fun f => ys.flatMap fun g => [andTable f g, orTable f g]

def tables1 : List RowTable := literalTables
def tables2 : List RowTable := pairTables tables1 tables1
def tables3 : List RowTable := pairTables tables1 tables2 ++ pairTables tables2 tables1
def tables4 : List RowTable := pairTables tables1 tables3 ++ pairTables tables2 tables2 ++ pairTables tables3 tables1

def exactTables : Nat → List RowTable
  | 1 => tables1
  | 2 => tables2
  | 3 => tables3
  | 4 => tables4
  | _ => []

def formulaTable (φ : DMFormula 3) : RowTable := rowTable (fun r => φ.eval (rowInput r))

def majorityTable : RowTable := rowTable (fun r => majority3 (rowInput r))

lemma literal_mem (i : Fin 3) (b : Bool) : litTable i b ∈ literalTables := by
  fin_cases i <;> cases b <;> simp [literalTables, litTable]

lemma and_mem_pair {f g : RowTable} {xs ys : List RowTable}
    (hf : f ∈ xs) (hg : g ∈ ys) : andTable f g ∈ pairTables xs ys := by
  apply List.mem_flatMap.mpr
  refine ⟨f, hf, ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨g, hg, ?_⟩
  simp [andTable]

lemma or_mem_pair {f g : RowTable} {xs ys : List RowTable}
    (hf : f ∈ xs) (hg : g ∈ ys) : orTable f g ∈ pairTables xs ys := by
  apply List.mem_flatMap.mpr
  refine ⟨f, hf, ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨g, hg, ?_⟩
  simp [orTable]

lemma pair_mem_exact {m n : Nat} {t : RowTable}
    (hm : 1 ≤ m) (hn : 1 ≤ n) (hs : m + n ≤ 4)
    (h : t ∈ pairTables (exactTables m) (exactTables n)) :
    t ∈ exactTables (m + n) := by
  have hcases : (m = 1 ∧ n = 1) ∨ (m = 1 ∧ n = 2) ∨ (m = 2 ∧ n = 1) ∨
      (m = 1 ∧ n = 3) ∨ (m = 2 ∧ n = 2) ∨ (m = 3 ∧ n = 1) := by omega
  rcases hcases with h11 | h12 | h21 | h13 | h22 | h31
  · simpa [exactTables, tables1, tables2, h11.1, h11.2] using h
  · have h' : t ∈ pairTables (exactTables 1) (exactTables 2) := by
      simpa [h12.1, h12.2] using h
    have ha : t ∈ pairTables (exactTables 1) (exactTables 2) ++
        pairTables (exactTables 2) (exactTables 1) := List.mem_append.mpr (Or.inl h')
    simpa [exactTables, tables1, tables2, tables3, h12.1, h12.2] using ha
  · have h' : t ∈ pairTables (exactTables 2) (exactTables 1) := by
      simpa [h21.1, h21.2] using h
    have ha : t ∈ pairTables (exactTables 1) (exactTables 2) ++
        pairTables (exactTables 2) (exactTables 1) := List.mem_append.mpr (Or.inr h')
    simpa [exactTables, tables1, tables2, tables3, h21.1, h21.2] using ha
  · have h' : t ∈ pairTables (exactTables 1) (exactTables 3) := by
      simpa [h13.1, h13.2] using h
    have ha : t ∈ pairTables (exactTables 1) (exactTables 3) ++
        (pairTables (exactTables 2) (exactTables 2) ++ pairTables (exactTables 3) (exactTables 1)) :=
      List.mem_append.mpr (Or.inl h')
    simpa [exactTables, tables1, tables2, tables3, tables4, h13.1, h13.2] using ha
  · have h' : t ∈ pairTables (exactTables 2) (exactTables 2) := by
      simpa [h22.1, h22.2] using h
    have ha : t ∈ pairTables (exactTables 1) (exactTables 3) ++
        (pairTables (exactTables 2) (exactTables 2) ++ pairTables (exactTables 3) (exactTables 1)) :=
      List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inl h')))
    simpa [exactTables, tables1, tables2, tables3, tables4, h22.1, h22.2] using ha
  · have h' : t ∈ pairTables (exactTables 3) (exactTables 1) := by
      simpa [h31.1, h31.2] using h
    have ha : t ∈ pairTables (exactTables 1) (exactTables 3) ++
        (pairTables (exactTables 2) (exactTables 2) ++ pairTables (exactTables 3) (exactTables 1)) :=
      List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr h')))
    simpa [exactTables, tables1, tables2, tables3, tables4, h31.1, h31.2] using ha

theorem formulaTable_mem_exact (φ : DMFormula 3) (hφ : φ.leaves ≤ 4) :
    formulaTable φ ∈ exactTables φ.leaves := by
  induction φ with
  | lit i b =>
      simpa [DMFormula.leaves, exactTables, tables1, formulaTable, litTable, DMFormula.eval]
        using literal_mem i b
  | and p q ihp ihq =>
      have hpPos := leaves_pos p
      have hqPos := leaves_pos q
      have hsum : p.leaves + q.leaves ≤ 4 := by simpa [DMFormula.leaves] using hφ
      have hpBound : p.leaves ≤ 4 := by omega
      have hqBound : q.leaves ≤ 4 := by omega
      have hout := and_mem_pair (ihp hpBound) (ihq hqBound)
      change rowTable (fun r => p.eval (rowInput r) && q.eval (rowInput r)) ∈
        exactTables (p.leaves + q.leaves)
      rw [rowTable_and]
      exact pair_mem_exact hpPos hqPos hsum hout
  | or p q ihp ihq =>
      have hpPos := leaves_pos p
      have hqPos := leaves_pos q
      have hsum : p.leaves + q.leaves ≤ 4 := by simpa [DMFormula.leaves] using hφ
      have hpBound : p.leaves ≤ 4 := by omega
      have hqBound : q.leaves ≤ 4 := by omega
      have hout := or_mem_pair (ihp hpBound) (ihq hqBound)
      change rowTable (fun r => p.eval (rowInput r) || q.eval (rowInput r)) ∈
        exactTables (p.leaves + q.leaves)
      rw [rowTable_or]
      exact pair_mem_exact hpPos hqPos hsum hout

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem majorityTable_not_small :
    majorityTable ∉ (exactTables 1 ++ exactTables 2 ++ exactTables 3 ++ exactTables 4) := by
  intro h
  have hmem := List.elem_eq_true_of_mem h
  have hfalse : List.elem majorityTable
      (exactTables 1 ++ exactTables 2 ++ exactTables 3 ++ exactTables 4) = false := by rfl
  rw [hfalse] at hmem
  cases hmem

theorem triangle3_not_has_leaf_size_four : ¬ HasLeafSize 3 majority3 4 := by
  rintro ⟨φ, hsize, heval⟩
  have hmem := formulaTable_mem_exact φ hsize
  have htable : formulaTable φ = majorityTable := by
    apply rowTable_congr
    intro r
    exact heval (rowInput r)
  rw [htable] at hmem
  have hcases : φ.leaves = 1 ∨ φ.leaves = 2 ∨ φ.leaves = 3 ∨ φ.leaves = 4 := by
    have := leaves_pos φ
    omega
  rcases hcases with h | h | h | h
  · apply majorityTable_not_small
    simp only [List.mem_append]
    exact Or.inl (Or.inl (Or.inl (by simpa [h] using hmem)))
  · apply majorityTable_not_small
    simp only [List.mem_append]
    exact Or.inl (Or.inl (Or.inr (by simpa [h] using hmem)))
  · apply majorityTable_not_small
    simp only [List.mem_append]
    exact Or.inl (Or.inr (by simpa [h] using hmem))
  · apply majorityTable_not_small
    simp only [List.mem_append]
    exact Or.inr (by simpa [h] using hmem)

def triangle (x : Fin 5 → Bool) : Bool :=
  (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2)

def dropInput (x : Fin 3 → Bool) : Fin 5 → Bool := fun i =>
  if h : i.val < 3 then x ⟨i.val, h⟩ else false

def dropFormula : DMFormula 5 → RForm 3
  | .lit i b => if h : i.val < 3 then (false, some (.lit ⟨i.val, h⟩ b)) else (!b, none)
  | .and a b => rAnd (dropFormula a) (dropFormula b)
  | .or a b => rOr (dropFormula a) (dropFormula b)

theorem dropFormula_eval (φ : DMFormula 5) (x : Fin 3 → Bool) :
    rEval (dropFormula φ) x = φ.eval (dropInput x) := by
  induction φ with
  | lit i b =>
      by_cases h : i.val < 3
      · have hi : dropInput x i = x ⟨i.val, h⟩ := by simp [dropInput, h]
        simp [dropFormula, h, rEval, DMFormula.eval, hi]
      · have hi : dropInput x i = false := by simp [dropInput, h]
        cases b <;> simp [dropFormula, h, rEval, DMFormula.eval, hi]
  | and a b iha ihb =>
      simp only [dropFormula, rAnd_eval, iha, ihb, DMFormula.eval]
  | or a b iha ihb =>
      simp only [dropFormula, rOr_eval, iha, ihb, DMFormula.eval]

theorem dropFormula_size (φ : DMFormula 5) : rSize (dropFormula φ) ≤ φ.leaves := by
  induction φ with
  | lit i b => by_cases h : i.val < 3 <;> simp [dropFormula, rSize, DMFormula.leaves, h]
  | and a b iha ihb =>
      calc
        rSize (dropFormula (.and a b)) ≤ rSize (dropFormula a) + rSize (dropFormula b) := rAnd_size _ _
        _ ≤ a.leaves + b.leaves := Nat.add_le_add iha ihb
        _ = DMFormula.leaves (.and a b) := rfl
  | or a b iha ihb =>
      calc
        rSize (dropFormula (.or a b)) ≤ rSize (dropFormula a) + rSize (dropFormula b) := rOr_size _ _
        _ ≤ a.leaves + b.leaves := Nat.add_le_add iha ihb
        _ = DMFormula.leaves (.or a b) := rfl

theorem triangle_lower (φ : DMFormula 5) (he : ∀ x, φ.eval x = triangle x) : ¬ φ.leaves ≤ 4 := by
  intro hle
  let r := dropFormula φ
  have heval : ∀ x, rEval r x = majority3 x := by
    intro x
    calc
      rEval r x = φ.eval (dropInput x) := by simpa [r] using dropFormula_eval φ x
      _ = triangle (dropInput x) := he _
      _ = majority3 x := by simp [triangle, dropInput, majority3]
  cases hr : r.2 with
  | none =>
      have hfalse := heval (fun _ => false)
      have htrue := heval (fun i => decide (i.val < 2))
      simp [rEval, hr, majority3] at hfalse htrue
      have hbad : false = true := hfalse.symm.trans htrue
      cases hbad
  | some ψ =>
      have hψ : ∀ x, ψ.eval x = majority3 x := by
        intro x
        simpa [rEval, hr] using heval x
      have hsize : ψ.leaves ≤ 4 := by
        have hs := dropFormula_size φ
        simpa [r, rSize, hr] using le_trans hs hle
      exact triangle3_not_has_leaf_size_four ⟨ψ, hsize, hψ⟩

def target (x : Fin 5 → Bool) : Bool :=
  (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 0 && x 3) || (x 3 && x 4)

def cofactor0 (x : Fin 5 → Bool) : Bool :=
  (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 0 && x 3)

def cofactor1 (x : Fin 5 → Bool) : Bool :=
  (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || x 3

theorem target_cofactors (x : Fin 5 → Bool) :
    target (upd x 4 false) = cofactor0 x ∧ target (upd x 4 true) = cofactor1 x := by
  cases h3 : x 3 <;> simp [target, cofactor0, cofactor1, upd, h3]

theorem target_dep (i : Fin 5) : ∃ x c, target (upd x i c) ≠ target x := by
  fin_cases i
  · exact ⟨![false, true, false, false, false], true, by decide⟩
  · exact ⟨![true, false, false, false, false], true, by decide⟩
  · exact ⟨![true, false, false, false, false], true, by decide⟩
  · exact ⟨![false, false, false, false, true], true, by decide⟩
  · exact ⟨![false, false, false, true, false], true, by decide⟩

theorem cofactor_dep (f : (Fin 5 → Bool) → Bool) (i : Fin 5)
    (hdep : ∃ x c, f (upd x i c) ≠ f x) :
    ∀ φ : DMFormula 5, (∀ x, φ.eval x = f x) → 1 ≤ occ φ i := by
  intro φ he
  by_contra hzero
  have hz : occ φ i = 0 := by omega
  obtain ⟨x, c, hx⟩ := hdep
  apply hx
  rw [← he, ← he]
  exact eval_upd_zero φ i hz x c

theorem cofactor_lower (f : (Fin 5 → Bool) → Bool)
    (hdep : ∃ x c, f (upd x 3 c) ≠ f x)
    (hzero : ∀ x, f (upd x 3 false) = triangle x) :
    ∀ φ : DMFormula 5, (∀ x, φ.eval x = f x) → 6 ≤ φ.leaves := by
  intro φ heφ
  have hocc := cofactor_dep f 3 hdep φ heφ
  let r := restrictR φ 3 false
  have hev : ∀ x, rEval r x = triangle x := by
    intro x
    calc
      rEval r x = φ.eval (upd x 3 false) := by simpa [r] using restrictR_eval φ 3 false x
      _ = f (upd x 3 false) := heφ _
      _ = triangle x := hzero x
  cases hr : r.2 with
  | none =>
    have hf := hev (fun _ => false)
    have ht := hev ![true, true, false, false, false]
    have hfalse : r.1 = false := by simpa [rEval, hr, triangle] using hf
    have htrue : r.1 = true := by simpa [rEval, hr, triangle] using ht
    have hbad : false = true := hfalse.symm.trans htrue
    cases hbad
  | some ψ =>
    have hψ : ∀ x, ψ.eval x = triangle x := by
      intro x
      simpa [rEval, hr] using hev x
    have htri : 5 ≤ ψ.leaves := by
      have hn := triangle_lower ψ hψ
      omega
    have hr' : (restrictR φ 3 false).2 = some ψ := by simpa [r] using hr
    have hsize : ψ.leaves ≤ φ.leaves - occ φ 3 := by
      simpa [r, rSize, hr'] using (restrictR_size φ 3 false)
    have hoccpos : 1 ≤ occ φ 3 := hocc
    omega

theorem cofactors_lower :
    (∀ φ : DMFormula 5, (∀ x, φ.eval x = cofactor0 x) → 6 ≤ φ.leaves) ∧
    (∀ φ : DMFormula 5, (∀ x, φ.eval x = cofactor1 x) → 6 ≤ φ.leaves) := by
  constructor
  · intro φ he
    exact cofactor_lower cofactor0
      ⟨![true, false, false, false, false], true, by decide⟩
      (by intro x; simp [cofactor0, upd, triangle]) φ he
  · intro φ he
    exact cofactor_lower cofactor1
      ⟨![true, false, false, false, false], true, by decide⟩
      (by intro x; simp [cofactor1, upd, triangle]) φ he

theorem lower_seven (φ : DMFormula 5) (hle : φ.leaves ≤ 7) (he : ∀ x, φ.eval x = target x) : False := by
  have hdep4 := cofactor_dep target 4 (target_dep 4) φ he
  have h0 : ∀ x, φ.eval (upd x 4 false) = cofactor0 x := by
    intro x
    calc
      φ.eval (upd x 4 false) = target (upd x 4 false) := he _
      _ = cofactor0 x := (target_cofactors x).1
  have h1 : ∀ x, φ.eval (upd x 4 true) = cofactor1 x := by
    intro x
    calc
      φ.eval (upd x 4 true) = target (upd x 4 true) := he _
      _ = cofactor1 x := (target_cofactors x).2
  let r0 := restrictR φ 4 false
  let r1 := restrictR φ 4 true
  have e0 : ∀ x, rEval r0 x = cofactor0 x := by
    intro x
    simpa [r0] using (restrictR_eval φ 4 false x).trans (h0 x)
  have e1 : ∀ x, rEval r1 x = cofactor1 x := by
    intro x
    simpa [r1] using (restrictR_eval φ 4 true x).trans (h1 x)
  have nonconst0 : r0.2.isSome := by
    cases h : r0.2 with
    | none =>
      have e0a := e0 (fun _ => false)
      have e0b := e0 ![true, true, false, false, false]
      have hfalse : r0.1 = false := by
        simpa [rEval, r0, h, cofactor0] using e0a
      have htrue : r0.1 = true := by
        simpa [rEval, r0, h, cofactor0] using e0b
      have hbad : false = true := hfalse.symm.trans htrue
      cases hbad
    | some ψ => simp
  have nonconst1 : r1.2.isSome := by
    cases h : r1.2 with
    | none =>
      have e1a := e1 (fun _ => false)
      have e1b := e1 ![false, false, false, true, false]
      have hfalse : r1.1 = false := by
        simpa [rEval, r1, h, cofactor1] using e1a
      have htrue : r1.1 = true := by
        simpa [rEval, r1, h, cofactor1] using e1b
      have hbad : false = true := hfalse.symm.trans htrue
      cases hbad
    | some ψ => simp
  obtain ⟨ψ0, hψ0⟩ := Option.isSome_iff_exists.mp nonconst0
  obtain ⟨ψ1, hψ1⟩ := Option.isSome_iff_exists.mp nonconst1
  have hψ0eval : ∀ x, ψ0.eval x = cofactor0 x := by
    intro x
    have := e0 x
    simpa [rEval, r0, hψ0] using this
  have hψ1eval : ∀ x, ψ1.eval x = cofactor1 x := by
    intro x
    have := e1 x
    simpa [rEval, r1, hψ1] using this
  have hsize0 := (cofactors_lower.1 ψ0 hψ0eval)
  have hsize1 := (cofactors_lower.2 ψ1 hψ1eval)
  have hr0 : rSize (restrictR φ 4 false) = ψ0.leaves := by
    simp [rSize, r0, hψ0]
  have hr1 : rSize (restrictR φ 4 true) = ψ1.leaves := by
    simp [rSize, r1, hψ1]
  by_cases ho : occ φ 4 = 1
  · have hn : ∀ s, φ ≠ .lit 4 s := by
      intro s hs
      subst hs
      simp [r0, restrictR] at hψ0
    have hp := single_pair_size φ 4 ho hn
    rw [hr0, hr1] at hp
    omega
  · have ho2 : 2 ≤ occ φ 4 := by omega
    have hs0 := restrictR_size φ 4 false
    rw [hr0] at hs0
    omega

def upper : DMFormula 5 :=
  .or (.or (.and (.lit 0 true) (.or (.or (.lit 1 true) (.lit 2 true)) (.lit 3 true)))
    (.and (.lit 1 true) (.lit 2 true))) (.and (.lit 3 true) (.lit 4 true))

theorem upper_leaves : upper.leaves ≤ 8 := by decide

theorem upper_eval : ∀ x, upper.eval x = target x := by
  intro x
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;> cases h4 : x 4 <;>
    simp [upper, target, DMFormula.eval, h0, h1, h2, h3, h4]

end PEqualNP.Outside.L_meta_185

theorem PEqualNP.Outside.L_meta_185 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasLeafSize 5 (fun x : Fin 5 → Bool =>
      (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 0 && x 3) || (x 3 && x 4)) s ↔ 8 ≤ s := by
  intro s
  constructor
  · rintro ⟨φ, hle, he⟩
    by_contra hs
    have h7 : φ.leaves ≤ 7 := by omega
    exact L_meta_185.lower_seven φ h7 he
  · intro hs
    unfold PEqualNP.MetaComplexity.HasLeafSize
    refine ⟨L_meta_185.upper, ?_, ?_⟩
    · exact Nat.le_trans L_meta_185.upper_leaves hs
    · exact L_meta_185.upper_eval
