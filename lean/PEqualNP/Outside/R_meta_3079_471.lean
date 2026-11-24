import Mathlib
import PEqualNP.Defs
-- The last gate is read at its actual output index, so gates after it disappear.
-- A final NOT needs an earlier NOT because the target separates the zero and all-one rows.
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8192 in
theorem PEqualNP.Outside.R_meta_3079_471
    (meet : ∀ (a b : Fin 10) (P : List (Fin 3 × Fin 26 × Fin 26)), a ≤ b → P.length ≤ 12 →
      let rd := fun (w : List Bool) (i : Fin 26) => if i.val = 25 then true else w.getD i.val false
      let base := fun (r : Fin 512) =>
        let m : ℕ := r.val
        let x := fun i : Fin 9 => m.testBit i.val
        let w := List.ofFn x
        w ++ [x 0 || x 4,w.getD a.val false || w.getD b.val false]
      let W (r : Fin 512) := P.foldl (fun (w : List Bool) (g : Fin 3 × Fin 26 × Fin 26) =>
        w ++ [if g.1.val = 0 then rd w g.2.1 && rd w g.2.2 else
              if g.1.val = 1 then rd w g.2.1 || rd w g.2.2 else !rd w g.2.1]) (base r)
      let F := fun (r : Fin 512) => let m : ℕ := r.val; ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any fun e => m.testBit (e / 10) && m.testBit (e % 10)
      ∀ i j, (∀ r, F r = true → rd (W r) i = true ∧ rd (W r) j = true) →
        ∃ r, F r = false ∧ rd (W r) i = true ∧ rd (W r) j = true)
    (join : ∀ (a b : Fin 10) (P : List (Fin 3 × Fin 26 × Fin 26)), a ≤ b → P.length ≤ 12 →
      let rd := fun (w : List Bool) (i : Fin 26) => if i.val = 25 then true else w.getD i.val false
      let base := fun (r : Fin 512) =>
        let m : ℕ := r.val
        let x := fun i : Fin 9 => m.testBit i.val
        let w := List.ofFn x
        w ++ [x 0 || x 4,w.getD a.val false || w.getD b.val false]
      let W (r : Fin 512) := P.foldl (fun (w : List Bool) (g : Fin 3 × Fin 26 × Fin 26) =>
        w ++ [if g.1.val = 0 then rd w g.2.1 && rd w g.2.2 else
              if g.1.val = 1 then rd w g.2.1 || rd w g.2.2 else !rd w g.2.1]) (base r)
      let F := fun (r : Fin 512) => let m : ℕ := r.val; ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any fun e => m.testBit (e / 10) && m.testBit (e % 10)
      ∀ i j, (∀ r, F r = false → rd (W r) i = false ∧ rd (W r) j = false) →
        ∃ r, F r = true ∧ rd (W r) i = false ∧ rd (W r) j = false)
    (neg : ∀ (a b : Fin 10) (P : List (Fin 3 × Fin 26 × Fin 26)), a ≤ b → P.length ≤ 12 →
      let rd := fun (w : List Bool) (i : Fin 26) => if i.val = 25 then true else w.getD i.val false
      let base := fun (r : Fin 512) =>
        let m : ℕ := r.val
        let x := fun i : Fin 9 => m.testBit i.val
        let w := List.ofFn x
        w ++ [x 0 || x 4,w.getD a.val false || w.getD b.val false]
      let W (r : Fin 512) := P.foldl (fun (w : List Bool) (g : Fin 3 × Fin 26 × Fin 26) =>
        w ++ [if g.1.val = 0 then rd w g.2.1 && rd w g.2.2 else
              if g.1.val = 1 then rd w g.2.1 || rd w g.2.2 else !rd w g.2.1]) (base r)
      let F := fun (r : Fin 512) => let m : ℕ := r.val; ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any fun e => m.testBit (e / 10) && m.testBit (e % 10)
      (∃ g ∈ P, g.1.val = 2) → ∀ i, ∃ r, rd (W r) i = F r)
    : ∀ (x1 x2 x3 : Fin (26 : ℕ)) (x4 : List (Fin (3 : ℕ) × Fin (26 : ℕ) × Fin (26 : ℕ))),   x4.length ≤ (13 : ℕ) →     ↑x1 ≠ (9 : ℕ) ∧ ↑x2 ≠ (9 : ℕ) →       ↑x1 ≠ (25 : ℕ) →         ↑x2 ≠ (25 : ℕ) →           (∀ x9 < (9 : ℕ), (∃ x11 ∈ x4, ↑x11.2.1 = x9 ∨ ↑x11.2.2 = x9) ∨ ↑x1 = x9 ∧ (↑x2 = x9 ∨ (10 : ℕ) ≤ ↑x2 ∨ (x9, ↑x2) ∈ [((0 : ℕ), (3 : ℕ)), ((4 : ℕ), (1 : ℕ)), ((4 : ℕ), (5 : ℕ))]) ∨ ↑x2 = x9 ∧ (↑x1 = x9 ∨ (10 : ℕ) ≤ ↑x1 ∨ (x9, ↑x1) ∈ [((0 : ℕ), (3 : ℕ)), ((4 : ℕ), (1 : ℕ)), ((4 : ℕ), (5 : ℕ))])) →             ∃ x10 < (512 : ℕ),               have x11 : Fin (9 : ℕ) → Bool := fun (x11 : Fin (9 : ℕ)) => x10.testBit ↑x11;               have x12 : List Bool → Fin (26 : ℕ) → Bool := fun (x12 : List Bool) (x13 : Fin (26 : ℕ)) => if ↑x13 = (25 : ℕ) then Bool.true else x12.getD (↑x13) Bool.false;               have x13 : List Bool := List.foldl (fun (x13 : List Bool) (x14 : Fin (3 : ℕ) × Fin (26 : ℕ) × Fin (26 : ℕ)) => x13 ++ [if ↑x14.1 = (0 : ℕ) then x12 x13 x14.2.1 && x12 x13 x14.2.2 else if ↑x14.1 = (1 : ℕ) then x12 x13 x14.2.1 || x12 x13 x14.2.2 else !x12 x13 x14.2.1]) (List.ofFn x11 ++ [x11 (0 : Fin (9 : ℕ)) || x11 (4 : Fin (9 : ℕ))]) (((1 : Fin (3 : ℕ)), x1, x2) :: x4);               x13.getD (↑x3) Bool.false ≠ [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x14 : ℕ) => x11 (Fin.ofNat (9 : ℕ) (x14 / (10 : ℕ))) && x11 (Fin.ofNat (9 : ℕ) (x14 % (10 : ℕ))) := by
  let rd := fun (w : List Bool) (i : Fin 26) => if i.val = 25 then true else w.getD i.val false
  let step := fun (w : List Bool) (g : Fin 3 × Fin 26 × Fin 26) =>
        w ++ [if g.1.val = 0 then rd w g.2.1 && rd w g.2.2 else
              if g.1.val = 1 then rd w g.2.1 || rd w g.2.2 else !rd w g.2.1]
  let base (a b : Fin 10) := fun (r : Fin 512) =>
        let x := fun i : Fin 9 => r.val.testBit i.val
        let w := List.ofFn x
        w ++ [x 0 || x 4,w.getD a.val false || w.getD b.val false]
  let F := fun (r : Fin 512) => ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any fun e => r.val.testBit (e / 10) && r.val.testBit (e % 10)
  have length (P : List (Fin 3 × Fin 26 × Fin 26)) (w : List Bool) :
      (P.foldl step w).length = w.length + P.length := by
    induction P generalizing w with
    | nil => simp
    | cons g gs ih =>
      rw [List.foldl_cons,ih]
      simp [step]
      omega
  have bl (a b : Fin 10) (r : Fin 512) : (base a b r).length = 11 := by simp [base]
  have atEnd (w : List Bool) (g : Fin 3 × Fin 26 × Fin 26) :
      (step w g).getD w.length false =
        (if g.1.val = 0 then rd w g.2.1 && rd w g.2.2 else
         if g.1.val = 1 then rd w g.2.1 || rd w g.2.2 else !rd w g.2.1) := by simp [step]
  have offEnd (w : List Bool) (g : Fin 3 × Fin 26 × Fin 26) (i : ℕ) (hi : i ≠ w.length) :
      (step w g).getD i false = w.getD i false := by
    by_cases h : i < w.length
    · exact List.getD_append _ _ _ _ h
    · rw [List.getD_eq_default _ _ (by simp [step];omega),List.getD_eq_default _ _ (by omega)]
  have pure (P : List (Fin 3 × Fin 26 × Fin 26)) (no : ∀ g ∈ P, g.1.val ≠ 2) :
      ∀ (x y : List Bool), x.length = y.length →
        (∀ i, rd x i = true → rd y i = true) →
          ∀ i, rd (P.foldl step x) i = true → rd (P.foldl step y) i = true := by
    induction P with
    | nil => exact fun _ _ _ h => h
    | cons g gs ih =>
      intro x y hl h
      apply ih (fun a ha => no a (List.mem_cons_of_mem _ ha)) _ _ (by simp [step,hl])
      intro i hx
      by_cases sentinel : i.val = 25
      · simp [rd,sentinel]
      simp only [rd,sentinel,ite_false] at hx ⊢
      by_cases last : i.val = x.length
      · rw [last,atEnd] at hx
        rw [last,hl,atEnd]
        have hnot := no g List.mem_cons_self
        have ho := g.1.isLt
        rcases (show g.1.val = 0 ∨ g.1.val = 1 by omega) with hz | hz
        · simp only [hz,ite_true,Bool.and_eq_true] at hx ⊢
          exact ⟨h _ hx.1,h _ hx.2⟩
        · simp only [hz,Nat.one_ne_zero,ite_false,ite_true,Bool.or_eq_true] at hx ⊢
          exact hx.imp (h _) (h _)
      · rw [offEnd _ _ _ last] at hx
        rw [offEnd _ _ _ (by omega)]
        simpa only [rd,sentinel,ite_false] using h i (by simpa only [rd,sentinel,ite_false] using hx)
  let singleton (i : ℕ) : Fin 512 := Fin.ofNat 512 (2^i)
  have single : ∀ i : Fin 9, F (singleton i.val) = false ∧ (singleton i.val).val.testBit i.val = true := by decide +kernel
  have starting (a b : Fin 10) (out : Fin 26) : ∃ r : Fin 512, (base a b r).getD out.val false ≠ F r := by
    by_cases raw : out.val < 9
    · let i : Fin 9 := ⟨out.val,raw⟩
      refine ⟨singleton i.val,?_⟩
      have spec := single i
      have hread : (base a b (singleton i.val)).getD out.val false = (singleton i.val).val.testBit i.val := by
        change (List.ofFn _ ++ _).getD _ false = _
        rw [List.getD_append _ _ _ _ (by simpa using raw),List.getD_eq_getElem _ _ (by simpa using raw),List.getElem_ofFn]
      rw [hread,spec.1,spec.2]; decide
    by_cases first : out.val = 9
    · refine ⟨12,?_⟩
      rw [first]
      have firstRead (a b : Fin 10) : (base a b 12).getD 9 false = false := by rfl
      rw [firstRead]; decide
    by_cases second : out.val = 10
    · let r := if a.val < 9 then singleton a.val else if b.val < 9 then singleton b.val else 3
      refine ⟨r,?_⟩
      rw [second]
      change (base a b (if a.val < 9 then singleton a.val else if b.val < 9 then singleton b.val else 3)).getD 10 false ≠ _
      have rawRead (c : Fin 10) (hc : c.val < 9) :
          (List.ofFn (fun i : Fin 9 => (singleton c.val).val.testBit i.val)).getD c.val false = true := by
        rw [List.getD_eq_getElem _ _ (by simpa using hc),List.getElem_ofFn]
        exact (single ⟨c.val,hc⟩).2
      have secRead (t : Fin 512) : (base a b t).getD 10 false =
          ((List.ofFn (fun i : Fin 9 => t.val.testBit i.val)).getD a.val false ||
           (List.ofFn (fun i : Fin 9 => t.val.testBit i.val)).getD b.val false) := by rfl
      by_cases ha : a.val < 9
      · simp only [ha,ite_true,secRead,rawRead a ha,Bool.true_or]
        exact (by simp [(single ⟨a.val,ha⟩).1,r,ha])
      · by_cases hb : b.val < 9
        · simp only [ha,hb,ite_false,ite_true,secRead,rawRead b hb,Bool.or_true]
          exact (by simp [(single ⟨b.val,hb⟩).1,r,ha,hb])
        · have za : a = 9 := Fin.ext (by have := a.isLt; change a.val = 9; omega)
          have zb : b = 9 := Fin.ext (by have := b.isLt; change b.val = 9; omega)
          subst a; subst b
          decide
    · refine ⟨3,?_⟩
      rw [List.getD_eq_default _ _ (by rw [bl];omega)]
      decide
  have baseLe (a b : Fin 10) (i : Fin 26) : rd (base a b 0) i = true → rd (base a b 511) i = true := by
    by_cases hi : i.val = 25
    · simp [rd,hi]
    · have zread : ∀ a : Fin 10, (List.ofFn (fun i : Fin 9 => (0 : Fin 512).val.testBit i.val)).getD a.val false = false := by decide +kernel
      have zeros (a b : Fin 10) : base a b 0 = List.replicate 11 false := by
        dsimp only [base]
        rw [zread a,zread b]
        rfl
      simp only [rd,hi,ite_false,zeros,List.getD_eq_getElem?_getD,List.getElem?_replicate]
      split <;> simp
  have impossible (a b : Fin 10) (order : a ≤ b) (out : Fin 26) (P : List (Fin 3 × Fin 26 × Fin 26)) :
      P.length ≤ 13 → ¬∀ r, (P.foldl step (base a b r)).getD out.val false = F r := by
    induction P using List.reverseRecOn with
    | nil =>
      intro _ good
      obtain ⟨r,hr⟩ := starting a b out
      exact hr (good r)
    | append_singleton P g ih =>
      intro hlen good
      have hh : P.length ≤ 12 := by simp only [List.length_append,List.length_singleton] at hlen; omega
      let W (r : Fin 512) := P.foldl step (base a b r)
      have wl (r : Fin 512) : (W r).length = 11 + P.length := by change (P.foldl step (base a b r)).length = _; rw [length,bl]
      have last (r : Fin 512) : (step (W r) g).getD out.val false = F r := by
        simpa only [List.foldl_append,List.foldl_cons,List.foldl_nil,W] using good r
      by_cases hend : out.val = 11 + P.length
      · have val (r : Fin 512) := last r
        have run (r : Fin 512) :
            (if g.1.val = 0 then rd (W r) g.2.1 && rd (W r) g.2.2 else
             if g.1.val = 1 then rd (W r) g.2.1 || rd (W r) g.2.2 else !rd (W r) g.2.1) = F r := by
          have h := last r
          rw [hend,←wl r,atEnd] at h
          exact h
        have opLT := g.1.isLt
        rcases (show g.1.val = 0 ∨ g.1.val = 1 ∨ g.1.val = 2 by omega) with hz | hz | hz
        · have h (r) : (rd (W r) g.2.1 && rd (W r) g.2.2) = F r := by simpa [hz] using run r
          obtain ⟨r,hf,h1,h2⟩ := meet a b P order hh g.2.1 g.2.2 (fun r hr => by simpa only [Bool.and_eq_true] using (h r).trans hr)
          change rd (W r) g.2.1 = _ at h1
          change rd (W r) g.2.2 = _ at h2
          change F r = _ at hf
          have bad := h r
          rw [h1,h2,hf] at bad
          contradiction
        · have h (r) : (rd (W r) g.2.1 || rd (W r) g.2.2) = F r := by simpa [hz] using run r
          obtain ⟨r,hf,h1,h2⟩ := join a b P order hh g.2.1 g.2.2 (fun r hr => Bool.or_eq_false_iff.mp ((h r).trans hr))
          change rd (W r) g.2.1 = _ at h1
          change rd (W r) g.2.2 = _ at h2
          change F r = _ at hf
          have bad := h r
          rw [h1,h2,hf] at bad
          contradiction
        · have h (r) : (!rd (W r) g.2.1) = F r := by simpa [hz] using run r
          have earlier : ∃ c ∈ P, c.1.val = 2 := by
            by_contra! hno
            have hx := h 0
            have hy := h 511
            have lo : F 0 = false := by decide
            have hi : F 511 = true := by decide
            rw [lo] at hx
            rw [hi] at hy
            have mono := pure P hno _ _ ((bl a b 0).trans (bl a b 511).symm) (baseLe a b) g.2.1
            change rd (W 0) g.2.1 = true → rd (W 511) g.2.1 = true at mono
            cases u : rd (W 0) g.2.1 <;> cases v : rd (W 511) g.2.1 <;> simp [u,v] at hx hy mono
          obtain ⟨r,hr⟩ := neg a b P order hh earlier g.2.1
          change rd (W r) g.2.1 = F r at hr
          have bad := h r
          rw [hr] at bad
          cases z : F r <;> simp [z] at bad
      · apply ih (by omega)
        intro r
        have l := last r
        rw [offEnd _ _ _ (fun eq => hend (eq.trans (wl r)))] at l
        exact l
  intro u v out P hlen hnine hu hv _coverage
  by_contra! good
  let norm (i : Fin 26) : Fin 10 := if hi : i.val < 9 then ⟨i.val,by omega⟩ else 9
  have project (x : Fin 9 → Bool) (i : Fin 26) (h9 : i.val ≠ 9) (h25 : i.val ≠ 25) :
      rd (List.ofFn x ++ [x 0 || x 4]) i = (List.ofFn x).getD (norm i).val false := by
    simp only [rd,h25,ite_false]
    by_cases hi : i.val < 9
    · rw [List.getD_append _ _ _ _ (by simpa using hi)]
      simp [norm,hi]
    · have hge : 10 ≤ i.val := by omega
      rw [List.getD_eq_default _ _ (by simp;omega)]
      simp [norm,hi]
  let a := norm u
  let b := norm v
  have unordered (r : Fin 512) : base (min a b) (max a b) r = base a b r := by
    rcases le_total a b with h | h
    · rw [min_eq_left h,max_eq_right h]
    · simp only [min_eq_right h,max_eq_left h,base,Bool.or_comm]
  apply impossible (min a b) (max a b) (min_le_max) out P hlen
  intro r
  let x (i : Fin 9) := r.val.testBit i.val
  have h := not_ne_iff.mp (good r.val r.isLt)
  change (P.foldl step ((List.ofFn x ++ [x 0 || x 4]) ++
      [rd (List.ofFn x ++ [x 0 || x 4]) u || rd (List.ofFn x ++ [x 0 || x 4]) v])).getD out.val false = _ at h
  rw [project x u hnine.1 hu, project x v hnine.2 hv] at h
  rw [unordered]
  exact h
