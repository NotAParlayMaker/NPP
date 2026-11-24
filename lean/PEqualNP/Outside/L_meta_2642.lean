import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2642_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.CircuitMoves

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma wiresFrom_append (gs1 gs2 : List Gate) (w : List Bool) :
    wiresFrom (gs1 ++ gs2) w = wiresFrom gs2 (wiresFrom gs1 w) := by
  simp [wiresFrom, List.foldl_append]

lemma wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    set b := g.op.eval (g.inputs.map fun i => w.getD i false)
    obtain ⟨t, ht, hlen⟩ := ih (w ++ [b])
    refine ⟨b :: t, ?_, by simp [hlen]⟩
    change wiresFrom gs (w ++ [b]) = w ++ b :: t
    rw [ht, List.append_assoc]
    rfl

lemma wiresFrom_length (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hlen⟩ := wiresFrom_prefix gs w
  rw [ht, List.length_append, hlen]

lemma wiresFrom_getD_lt (gs : List Gate) (w : List Bool) {i : ℕ} (hi : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge_length (w : List Bool) {i : ℕ} (hi : w.length ≤ i) :
    w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma getD_append_last (w : List Bool) (b : Bool) :
    (w ++ [b]).getD w.length false = b := by
  simp [List.getD_eq_getElem?_getD]

lemma getD_append_lt (w : List Bool) (b : Bool) {i : ℕ} (hi : i < w.length) :
    (w ++ [b]).getD i false = w.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

/-- Lockstep invariant for erasing gate `j` (at wire `m = n + j`) with redirect `r`. -/
lemma wiresFrom_erase_lockstep (n j r : ℕ) (gs : List Gate) :
    ∀ (A B : List Bool),
      n + j ≤ A.length →
      B.length = A.length + 1 →
      (∀ i < n + j, A.getD i false = B.getD i false) →
      (∀ i, n + j ≤ i → A.getD i false = B.getD (i + 1) false) →
      ((r < n + j ∧ B.getD (n + j) false = B.getD r false) ∨
       (A.length + gs.length < r ∧ B.getD (n + j) false = false) ∨
       (∀ g ∈ gs, n + j ∉ g.inputs)) →
      let A' := wiresFrom (gs.map (fun g => ⟨g.op, g.inputs.map (eraseRedirect n j r)⟩)) A
      let B' := wiresFrom gs B
      (∀ i < n + j, A'.getD i false = B'.getD i false) ∧
      (∀ i, n + j ≤ i → A'.getD i false = B'.getD (i + 1) false) := by
  induction gs with
  | nil =>
    intro A B _ _ hlt hge _
    exact ⟨hlt, hge⟩
  | cons g gs ih =>
    intro A B hAlen hBlen hlt hge hcond
    have hmap : (g.inputs.map (eraseRedirect n j r)).map (fun i => A.getD i false) =
        g.inputs.map (fun i => B.getD i false) := by
      rw [List.map_map]
      apply List.map_congr_left
      intro i hi
      dsimp only [Function.comp_apply, eraseRedirect]
      by_cases heq : i = n + j
      · subst heq
        rw [if_pos rfl]
        rcases hcond with ⟨hrlt, hbr⟩ | ⟨hrgt, hbf⟩ | hno
        · rw [hlt r hrlt, hbr]
        · rw [getD_ge_length A (by simp at hrgt; omega), hbf]
        · exact absurd hi (hno g (by simp))
      · rw [if_neg heq]
        by_cases hgt : n + j < i
        · rw [if_pos hgt]
          have h1 := hge (i - 1) (by omega)
          rwa [Nat.sub_add_cancel (by omega)] at h1
        · rw [if_neg hgt]
          exact hlt i (by omega)
    set bA := g.op.eval ((g.inputs.map (eraseRedirect n j r)).map (fun i => A.getD i false))
    set bB := g.op.eval (g.inputs.map (fun i => B.getD i false))
    have hb : bA = bB := congrArg g.op.eval hmap
    change
      let A' := wiresFrom (gs.map (fun g => ⟨g.op, g.inputs.map (eraseRedirect n j r)⟩)) (A ++ [bA])
      let B' := wiresFrom gs (B ++ [bB])
      (∀ i < n + j, A'.getD i false = B'.getD i false) ∧
      (∀ i, n + j ≤ i → A'.getD i false = B'.getD (i + 1) false)
    apply ih (A ++ [bA]) (B ++ [bB]) (by simp; omega) (by simp [hBlen])
    · intro i hi
      rw [getD_append_lt A bA (by omega), getD_append_lt B bB (by omega)]
      exact hlt i hi
    · intro i hi
      by_cases hltA : i < A.length
      · rw [getD_append_lt A bA hltA, getD_append_lt B bB (by omega)]
        exact hge i hi
      · by_cases heqA : i = A.length
        · subst heqA
          rw [getD_append_last A bA, ← hBlen, getD_append_last B bB, hb]
        · rw [getD_ge_length (A ++ [bA]) (by simp; omega),
              getD_ge_length (B ++ [bB]) (by simp; omega)]
    · rcases hcond with ⟨hrlt, hbr⟩ | ⟨hrgt, hbf⟩ | hno
      · left
        refine ⟨hrlt, ?_⟩
        rw [getD_append_lt B bB (by omega), getD_append_lt B bB (by omega)]
        exact hbr
      · right; left
        refine ⟨by simp at hrgt ⊢; omega, ?_⟩
        rw [getD_append_lt B bB (by omega)]
        exact hbf
      · right; right
        intro g' hg'
        exact hno g' (by simp [hg'])

lemma fanInTwo_eraseGate (n : ℕ) (C : Circuit) (j r : ℕ) (hF : FanInTwo C) :
    FanInTwo (eraseGate n C j r) := by
  unfold eraseGate
  split_ifs with hj
  · intro g hg
    simp only [List.mem_append, List.mem_map] at hg
    rcases hg with h1 | ⟨g0, hg0, rfl⟩
    · exact hF g (List.mem_of_mem_take h1)
    · have h0 := hF g0 (List.mem_of_mem_drop hg0)
      exact ⟨h0.1, by simpa using h0.2⟩
  · exact hF

lemma size_eraseGate (n : ℕ) (C : Circuit) (j r : ℕ) (hj : j < C.size) :
    (eraseGate n C j r).size + 1 = C.size := by
  unfold Circuit.size at hj ⊢
  unfold eraseGate
  rw [if_pos hj]
  simp only [List.length_append, List.length_take, List.length_map, List.length_drop]
  omega

lemma eval_eraseGate (n : ℕ) (C : Circuit) (j r : ℕ) (y : Fin n → Bool)
    (hj : j < C.size)
    (hr : r < n + j ∨ n + C.size ≤ r)
    (hstep :
      (C.wires (List.ofFn y)).getD (n + j) false = (C.wires (List.ofFn y)).getD r false ∨
      (C.output ≠ n + j ∧ ∀ g ∈ C.gates.drop (j + 1), n + j ∉ g.inputs)) :
    (eraseGate n C j r).eval (List.ofFn y) = C.eval (List.ofFn y) := by
  unfold Circuit.size at hj hr
  have hsplit : C.gates = C.gates.take j ++ [C.gates[j]] ++ C.gates.drop (j + 1) := by
    have h1 := (List.take_append_drop j C.gates).symm
    have h2 : C.gates.drop j = C.gates[j] :: C.gates.drop (j + 1) := List.drop_eq_getElem_cons hj
    rw [h2] at h1
    simpa [List.append_assoc] using h1
  set A0 := wiresFrom (C.gates.take j) (List.ofFn y)
  have hA0len : A0.length = n + j := by
    rw [wiresFrom_length, List.length_ofFn, List.length_take]
    omega
  set gj := C.gates[j]
  set bj := gj.op.eval (gj.inputs.map fun i => A0.getD i false)
  set B0 := A0 ++ [bj]
  have hB0len : B0.length = n + j + 1 := by simp [B0, hA0len]
  have hCw : C.wires (List.ofFn y) = wiresFrom (C.gates.drop (j + 1)) B0 := by
    unfold Circuit.wires
    change wiresFrom C.gates (List.ofFn y) = wiresFrom (C.gates.drop (j + 1)) B0
    conv_lhs => rw [hsplit]
    rw [wiresFrom_append, wiresFrom_append]
    rfl
  have hEw : (eraseGate n C j r).wires (List.ofFn y) =
      wiresFrom ((C.gates.drop (j + 1)).map (fun g => ⟨g.op, g.inputs.map (eraseRedirect n j r)⟩)) A0 := by
    unfold eraseGate Circuit.wires
    rw [if_pos hj]
    change wiresFrom (C.gates.take j ++ _) (List.ofFn y) = _
    rw [wiresFrom_append]
  have hB0_nj : B0.getD (n + j) false = (C.wires (List.ofFn y)).getD (n + j) false := by
    rw [hCw, wiresFrom_getD_lt _ B0 (by omega)]
  have hcond :
      (r < n + j ∧ B0.getD (n + j) false = B0.getD r false) ∨
      (A0.length + (C.gates.drop (j + 1)).length < r ∧ B0.getD (n + j) false = false) ∨
      (∀ g ∈ C.gates.drop (j + 1), n + j ∉ g.inputs) := by
    rcases hstep with heq | ⟨_, hno⟩
    · rcases hr with hrlt | hrge
      · left
        refine ⟨hrlt, ?_⟩
        rw [hB0_nj, heq, hCw, wiresFrom_getD_lt _ B0 (by omega)]
      · right; left
        refine ⟨by simp [hA0len]; omega, ?_⟩
        rw [hB0_nj, heq, getD_ge_length]
        rw [hCw, wiresFrom_length, hB0len, List.length_drop]
        omega
    · right; right; exact hno
  have hlock := wiresFrom_erase_lockstep n j r (C.gates.drop (j + 1)) A0 B0
    (by omega) (by omega)
    (fun i hi => by rw [getD_append_lt A0 bj (by omega)])
    (fun i hi => by
      rw [getD_ge_length A0 (by omega), getD_ge_length B0 (by omega)])
    hcond
  unfold Circuit.eval
  rw [hEw]
  have hout : (eraseGate n C j r).output = eraseRedirect n j r C.output := by
    unfold eraseGate; rw [if_pos hj]
  rw [hout]
  dsimp only [eraseRedirect]
  by_cases ho : C.output = n + j
  · rw [if_pos ho, ho]
    rcases hstep with heq | ⟨hne, _⟩
    · rcases hr with hrlt | hrge
      · rw [hlock.1 r hrlt, ← hCw, heq]
      · rw [getD_ge_length, heq, getD_ge_length]
        · rw [hCw, wiresFrom_length, hB0len, List.length_drop]; omega
        · rw [wiresFrom_length, hA0len, List.length_map, List.length_drop]; omega
    · exact absurd ho hne
  · rw [if_neg ho]
    by_cases hgt : n + j < C.output
    · rw [if_pos hgt]
      have h1 := hlock.2 (C.output - 1) (by omega)
      rw [Nat.sub_add_cancel (by omega), ← hCw] at h1
      exact h1
    · rw [if_neg hgt, hlock.1 C.output (by omega), ← hCw]

/-- Hardwire two inputs `u, v` to `false` by redirecting reads of `u, v` to an out-of-bounds wire. -/
def hardwireTwo (n : ℕ) (u v : Fin n) (C : Circuit) : Circuit :=
  let dead := n + C.size
  let redir := fun i => if i = u.val ∨ i = v.val then dead else i
  { gates := C.gates.map (fun g => ⟨g.op, g.inputs.map redir⟩)
    output := redir C.output }

lemma fanInTwo_hardwireTwo (n : ℕ) (u v : Fin n) (C : Circuit) (hF : FanInTwo C) :
    FanInTwo (hardwireTwo n u v C) := by
  intro g hg
  unfold hardwireTwo at hg
  simp only [List.mem_map] at hg
  obtain ⟨g0, hg0, rfl⟩ := hg
  have h0 := hF g0 hg0
  exact ⟨h0.1, by simpa using h0.2⟩

lemma size_hardwireTwo (n : ℕ) (u v : Fin n) (C : Circuit) :
    (hardwireTwo n u v C).size = C.size := by
  simp [hardwireTwo, Circuit.size]

lemma wiresFrom_hardwire_lockstep (n : ℕ) (u v : Fin n) (dead : ℕ) (gs : List Gate) :
    let redir := fun i => if i = u.val ∨ i = v.val then dead else i
    ∀ (A B : List Bool),
      A.length = B.length →
      n ≤ B.length →
      B.length + gs.length ≤ dead →
      B.getD u.val false = false →
      B.getD v.val false = false →
      (∀ i, i ≠ u.val → i ≠ v.val → A.getD i false = B.getD i false) →
      let A' := wiresFrom (gs.map (fun g => ⟨g.op, g.inputs.map redir⟩)) A
      let B' := wiresFrom gs B
      A'.length = B'.length ∧
      B'.getD u.val false = false ∧
      B'.getD v.val false = false ∧
      (∀ i, i ≠ u.val → i ≠ v.val → A'.getD i false = B'.getD i false) := by
  intro redir
  induction gs with
  | nil =>
    intro A B hlen _ _ hu hv hag
    exact ⟨hlen, hu, hv, hag⟩
  | cons g gs ih =>
    intro A B hlen hBn hdead hu hv hag
    have hmap : (g.inputs.map redir).map (fun i => A.getD i false) =
        g.inputs.map (fun i => B.getD i false) := by
      rw [List.map_map]
      apply List.map_congr_left
      intro i _
      dsimp only [Function.comp_apply, redir]
      by_cases h : i = u.val ∨ i = v.val
      · rw [if_pos h, getD_ge_length A (by omega)]
        rcases h with rfl | rfl
        · exact hu.symm
        · exact hv.symm
      · rw [if_neg h]
        push Not at h
        exact hag i h.1 h.2
    set bA := g.op.eval ((g.inputs.map redir).map (fun i => A.getD i false))
    set bB := g.op.eval (g.inputs.map (fun i => B.getD i false))
    have hb : bA = bB := congrArg g.op.eval hmap
    change
      let A' := wiresFrom (gs.map (fun g => ⟨g.op, g.inputs.map redir⟩)) (A ++ [bA])
      let B' := wiresFrom gs (B ++ [bB])
      A'.length = B'.length ∧
      B'.getD u.val false = false ∧
      B'.getD v.val false = false ∧
      (∀ i, i ≠ u.val → i ≠ v.val → A'.getD i false = B'.getD i false)
    apply ih (A ++ [bA]) (B ++ [bB]) (by simp [hlen]) (by simp; omega) (by simp at hdead ⊢; omega)
    · rw [getD_append_lt B bB (by omega)]; exact hu
    · rw [getD_append_lt B bB (by omega)]; exact hv
    · intro i hiu hiv
      by_cases hlt : i < B.length
      · rw [getD_append_lt A bA (by omega), getD_append_lt B bB hlt]
        exact hag i hiu hiv
      · by_cases heq : i = B.length
        · subst heq
          rw [← hlen, getD_append_last A bA, hlen, getD_append_last B bB, hb]
        · rw [getD_ge_length (A ++ [bA]) (by simp; omega),
              getD_ge_length (B ++ [bB]) (by simp; omega)]

lemma eval_hardwireTwo (n : ℕ) (u v : Fin n) (C : Circuit) (x : Fin n → Bool) :
    (hardwireTwo n u v C).eval (List.ofFn x) =
      C.eval (List.ofFn (Function.update (Function.update x u false) v false)) := by
  set y := Function.update (Function.update x u false) v false
  have hyu : y u = false := by
    by_cases huv : u = v
    · subst huv; simp [y]
    · simp [y, huv]
  have hyv : y v = false := by simp [y]
  have hlock := wiresFrom_hardwire_lockstep n u v (n + C.size) C.gates
    (List.ofFn x) (List.ofFn y) (by simp) (by simp) (by simp [Circuit.size])
    (by simp [List.getD_eq_getElem?_getD, hyu])
    (by simp [List.getD_eq_getElem?_getD, hyv])
    (fun i hiu hiv => by
      by_cases hlt : i < n
      · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hlt, dite_true, Option.getD_some]
        have hu' : (⟨i, hlt⟩ : Fin n) ≠ u := fun h => hiu (congrArg Fin.val h)
        have hv' : (⟨i, hlt⟩ : Fin n) ≠ v := fun h => hiv (congrArg Fin.val h)
        simp [y, hu', hv']
      · rw [getD_ge_length (List.ofFn x) (by simp; omega),
            getD_ge_length (List.ofFn y) (by simp; omega)])
  unfold Circuit.eval hardwireTwo
  dsimp only
  change (wiresFrom (C.gates.map _) (List.ofFn x)).getD (if C.output = u.val ∨ C.output = v.val then n + C.size else C.output) false =
    (wiresFrom C.gates (List.ofFn y)).getD C.output false
  by_cases ho : C.output = u.val ∨ C.output = v.val
  · rw [if_pos ho, getD_ge_length]
    · rcases ho with h1 | h2
      · rw [h1, hlock.2.1]
      · rw [h2, hlock.2.2.1]
    · rw [hlock.1, wiresFrom_length, List.length_ofFn, Circuit.size]
  · rw [if_neg ho]
    push Not at ho
    exact hlock.2.2.2 C.output ho.1 ho.2

lemma main_proof (n k : ℕ) (u v : Fin n) (Cs : ℕ → Circuit)
    (hF0 : FanInTwo (Cs 0))
    (hSteps : ∀ t < k,
      ∃ (j r : ℕ),
        j < (Cs t).size ∧
        (r < n + j ∨ n + (Cs t).size ≤ r) ∧
        Cs (t + 1) = eraseGate n (Cs t) j r ∧
        ((∀ x : Fin n → Bool,
            let w := (Cs t).wires (List.ofFn (Function.update (Function.update x u false) v false))
            w.getD (n + j) false = w.getD r false) ∨
          (Cs t).output ≠ n + j ∧ ∀ g ∈ (Cs t).gates.drop (j + 1), n + j ∉ g.inputs)) :
    ∃ D : Circuit,
      FanInTwo D ∧
      D.size + k = (Cs 0).size ∧
      ∀ x : Fin n → Bool,
        D.eval (List.ofFn x) = (Cs 0).eval (List.ofFn (Function.update (Function.update x u false) v false)) := by
  have hind : ∀ t ≤ k,
      FanInTwo (Cs t) ∧
      (Cs t).size + t = (Cs 0).size ∧
      ∀ x : Fin n → Bool,
        (Cs t).eval (List.ofFn (Function.update (Function.update x u false) v false)) =
          (Cs 0).eval (List.ofFn (Function.update (Function.update x u false) v false)) := by
    intro t
    induction t with
    | zero =>
      intro _
      exact ⟨hF0, by omega, fun _ => rfl⟩
    | succ t ih =>
      intro htk
      obtain ⟨hFt, hSt, hEt⟩ := ih (by omega)
      obtain ⟨j, r, hj, hr, hnext, hcond⟩ := hSteps t (by omega)
      rw [hnext]
      refine ⟨fanInTwo_eraseGate n (Cs t) j r hFt, ?_, ?_⟩
      · have hs := size_eraseGate n (Cs t) j r hj; omega
      · intro x
        rw [eval_eraseGate n (Cs t) j r _ hj hr (hcond.imp (fun h => h x) id)]
        exact hEt x
  obtain ⟨hFk, hSk, hEk⟩ := hind k le_rfl
  refine ⟨hardwireTwo n u v (Cs k), fanInTwo_hardwireTwo n u v (Cs k) hFk, ?_, ?_⟩
  · rw [size_hardwireTwo]; exact hSk
  · intro x
    rw [eval_hardwireTwo, hEk x]

end PEqualNP.Outside.L_meta_2642_aux

theorem PEqualNP.Outside.L_meta_2642 : ∀ (x1 x2 : ℕ) (x3 x4 : Fin x1) (x5 : ℕ → PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.FanInTwo (x5 (0 : ℕ)) →     (∀ x7 < x2,         ∃ (x9 : ℕ) (x10 : ℕ),           x9 < (x5 x7).size ∧             (x10 < x1 + x9 ∨ x1 + (x5 x7).size ≤ x10) ∧               x5 (x7 + (1 : ℕ)) = PEqualNP.CircuitMoves.eraseGate x1 (x5 x7) x9 x10 ∧                 ((∀ (x11 : Fin x1 → Bool),                     have x12 : List Bool := (x5 x7).wires (List.ofFn (Function.update (Function.update x11 x3 Bool.false) x4 Bool.false));                     x12.getD (x1 + x9) Bool.false = x12.getD x10 Bool.false) ∨                   (x5 x7).output ≠ x1 + x9 ∧ ∀ x11 ∈ List.drop (x9 + (1 : ℕ)) (x5 x7).gates, x1 + x9 ∉ x11.inputs)) →       ∃ (x8 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x8 ∧ x8.size + x2 = (x5 (0 : ℕ)).size ∧ ∀ (x9 : Fin x1 → Bool), x8.eval (List.ofFn x9) = (x5 (0 : ℕ)).eval (List.ofFn (Function.update (Function.update x9 x3 Bool.false) x4 Bool.false)) :=
  PEqualNP.Outside.L_meta_2642_aux.main_proof
