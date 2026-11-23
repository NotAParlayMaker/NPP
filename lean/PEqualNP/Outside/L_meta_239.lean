import Mathlib
import PEqualNP.Defs

-- Over the full binary basis, every gate reads two wires. For a set `W` of wires below
-- `n + m`, the inputs on which the values of `W` depend number at most `m + |W|`: replacing the
-- last gate `n + m - 1` in `W` by the (at most two) wires it reads raises `|W|` by at most one
-- and lowers `m` by one. Applied to the output wire, the inputs that the circuit reads number at
-- most `s + 1`, and a function that depends on every input must read all `n` of them.

namespace PEqualNP.Outside.L_meta_239_proof

open PEqualNP.MetaComplexity

-- One evaluation step of a binary circuit, as in `BinaryCircuit.wires`.
def step (w : List Bool) (g : BinaryGate) : List Bool :=
  w ++ [g.op (w.getD g.left false) (w.getD g.right false)]

theorem length_foldl (gs : List BinaryGate) :
    ∀ w0 : List Bool, (gs.foldl step w0).length = w0.length + gs.length := by
  induction gs with
  | nil => intro w0; simp
  | cons g gs ih =>
    intro w0
    rw [List.foldl_cons, ih]
    simp [step]
    omega

theorem prefix_foldl (gs : List BinaryGate) : ∀ w0 : List Bool, w0 <+: gs.foldl step w0 := by
  induction gs with
  | nil => intro w0; simp
  | cons g gs ih =>
    intro w0
    rw [List.foldl_cons]
    exact (List.prefix_append _ _).trans (ih _)

theorem getD_of_prefix {l1 l2 : List Bool} (h : l1 <+: l2) (i : ℕ) (hi : i < l1.length) :
    l1.getD i false = l2.getD i false := by
  obtain ⟨t, rfl⟩ := h
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem getD_of_le {l : List Bool} (i : ℕ) (hi : l.length ≤ i) : l.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

-- The value of gate `m`, read off the full list of wires.
theorem getD_gate (gs : List BinaryGate) (w0 : List Bool) (m : ℕ) (hm : m < gs.length) :
    (gs.foldl step w0).getD (w0.length + m) false =
      gs[m].op (((gs.take m).foldl step w0).getD gs[m].left false)
        (((gs.take m).foldl step w0).getD gs[m].right false) := by
  have hsplit : gs = gs.take m ++ gs[m] :: gs.drop (m + 1) := by
    simp
  set p := (gs.take m).foldl step w0 with hp
  have hplen : p.length = w0.length + m := by
    rw [hp, length_foldl, List.length_take]
    omega
  have hfull : gs.foldl step w0 = (gs.drop (m + 1)).foldl step (step p gs[m]) := by
    conv_lhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_cons]
  rw [hfull, ← getD_of_prefix (prefix_foldl _ _)]
  · simp [step, hplen.symm, List.getD_eq_getElem?_getD]
  · simp [step, hplen]

-- The full wire list is an extension of the list after the first `m` gates.
theorem prefix_take (gs : List BinaryGate) (w0 : List Bool) (m : ℕ) :
    (gs.take m).foldl step w0 <+: gs.foldl step w0 := by
  conv_rhs => rw [← List.take_append_drop m gs]
  rw [List.foldl_append]
  exact prefix_foldl _ _

theorem wires_eq (C : BinaryCircuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

-- The value of wire `w` on input `x`.
def val {n : ℕ} (C : BinaryCircuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

theorem val_input {n : ℕ} (C : BinaryCircuit) (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    val C x w = x ⟨w, hw⟩ := by
  unfold val
  rw [wires_eq, ← getD_of_prefix (prefix_foldl _ _) w (by simpa using hw)]
  simp [List.getD_eq_getElem?_getD, hw]

theorem val_gate {n : ℕ} (C : BinaryCircuit) (x : Fin n → Bool) (m : ℕ)
    (hm : m < C.gates.length) :
    val C x (n + m) =
      C.gates[m].op (if C.gates[m].left < n + m then val C x C.gates[m].left else false)
        (if C.gates[m].right < n + m then val C x C.gates[m].right else false) := by
  unfold val
  rw [wires_eq]
  have h := getD_gate C.gates (List.ofFn x) m hm
  rw [List.length_ofFn] at h
  rw [h]
  have hpre := prefix_take C.gates (List.ofFn x) m
  have hplen : ((C.gates.take m).foldl step (List.ofFn x)).length = n + m := by
    rw [length_foldl, List.length_take, List.length_ofFn]
    omega
  congr 1
  · split_ifs with hl
    · exact getD_of_prefix hpre _ (by omega)
    · exact getD_of_le _ (by omega)
  · split_ifs with hr
    · exact getD_of_prefix hpre _ (by omega)
    · exact getD_of_le _ (by omega)

theorem val_beyond {n : ℕ} (C : BinaryCircuit) (x : Fin n → Bool) (w : ℕ)
    (hw : n + C.gates.length ≤ w) : val C x w = false := by
  unfold val
  apply getD_of_le
  rw [wires_eq, length_foldl, List.length_ofFn]
  exact hw

-- The count: the wires of `W`, all below `n + m`, depend on at most `m + |W|` inputs.
theorem dep_count {n : ℕ} (C : BinaryCircuit) :
    ∀ m : ℕ, m ≤ C.gates.length → ∀ W : Finset ℕ, (∀ w ∈ W, w < n + m) →
      ∃ D : Finset (Fin n), D.card ≤ m + W.card ∧
        ∀ x y : Fin n → Bool, (∀ i ∈ D, x i = y i) → ∀ w ∈ W, val C x w = val C y w := by
  intro m
  induction m with
  | zero =>
    intro _ W hW
    refine ⟨Finset.univ.filter (fun i : Fin n => i.val ∈ W), ?_, ?_⟩
    · rw [Nat.zero_add]
      apply Finset.card_le_card_of_injOn (fun i : Fin n => i.val)
      · intro i hi
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hi
        exact hi
      · intro i _ j _ h
        exact Fin.ext h
    · intro x y hxy w hw
      have hwn : w < n := by simpa using hW w hw
      rw [val_input C x w hwn, val_input C y w hwn]
      apply hxy
      simp [hw]
  | succ m ih =>
    intro hm W hW
    by_cases hmem : n + m ∈ W
    · set g := C.gates[m]'(by omega) with hg
      set W' : Finset ℕ :=
        W.erase (n + m) ∪ (({g.left, g.right} : Finset ℕ).filter (fun w => w < n + m)) with hW'
      have hW'lt : ∀ w ∈ W', w < n + m := by
        intro w hw
        rw [hW', Finset.mem_union] at hw
        rcases hw with hw | hw
        · have h1 := Finset.ne_of_mem_erase hw
          have h2 := hW w (Finset.mem_of_mem_erase hw)
          omega
        · exact (Finset.mem_filter.1 hw).2
      have hcard : W'.card ≤ W.card + 1 := by
        have h1 := Finset.card_union_le (W.erase (n + m))
          (({g.left, g.right} : Finset ℕ).filter (fun w => w < n + m))
        have h2 := Finset.card_erase_of_mem hmem
        have h3 := Finset.card_filter_le ({g.left, g.right} : Finset ℕ) (fun w => w < n + m)
        have h4 : ({g.left, g.right} : Finset ℕ).card ≤ 2 := Finset.card_le_two
        have h5 : 1 ≤ W.card := Finset.card_pos.2 ⟨_, hmem⟩
        rw [← hW'] at h1
        omega
      obtain ⟨D, hD, hDval⟩ := ih (by omega) W' hW'lt
      refine ⟨D, by omega, ?_⟩
      intro x y hxy w hw
      by_cases hwm : w = n + m
      · subst hwm
        have hmlt : m < C.gates.length := by omega
        rw [val_gate C x m hmlt, val_gate C y m hmlt]
        have hl : (if C.gates[m].left < n + m then val C x C.gates[m].left else false) =
            (if C.gates[m].left < n + m then val C y C.gates[m].left else false) := by
          split_ifs with h
          · apply hDval x y hxy
            rw [hW', Finset.mem_union]
            right
            exact Finset.mem_filter.2 ⟨by simp [hg], h⟩
          · rfl
        have hr : (if C.gates[m].right < n + m then val C x C.gates[m].right else false) =
            (if C.gates[m].right < n + m then val C y C.gates[m].right else false) := by
          split_ifs with h
          · apply hDval x y hxy
            rw [hW', Finset.mem_union]
            right
            exact Finset.mem_filter.2 ⟨by simp [hg], h⟩
          · rfl
        rw [hl, hr]
      · apply hDval x y hxy
        rw [hW', Finset.mem_union]
        left
        exact Finset.mem_erase.2 ⟨hwm, hw⟩
    · have hWlt : ∀ w ∈ W, w < n + m := by
        intro w hw
        have h1 := hW w hw
        have h2 : w ≠ n + m := fun h => hmem (h ▸ hw)
        omega
      obtain ⟨D, hD, hDval⟩ := ih (by omega) W hWlt
      exact ⟨D, by omega, hDval⟩

end PEqualNP.Outside.L_meta_239_proof

open PEqualNP.Outside.L_meta_239_proof in
theorem PEqualNP.Outside.L_meta_239 : ∀ (n : ℕ) (f : (Fin n → Bool) → Bool), (∀ i : Fin n, ∃ x : Fin n → Bool, f (Function.update x i (!x i)) ≠ f x) → ∀ s : ℕ, PEqualNP.MetaComplexity.HasBinarySize n f s → n ≤ s + 1 := by
  intro n f hdep s ⟨C, hsize, hC⟩
  set k := C.gates.length with hk
  set W : Finset ℕ := ({C.output} : Finset ℕ).filter (fun w => w < n + k) with hW
  have hWlt : ∀ w ∈ W, w < n + k := fun w hw => (Finset.mem_filter.1 hw).2
  have hWcard : W.card ≤ 1 := by
    have := Finset.card_filter_le ({C.output} : Finset ℕ) (fun w => w < n + k)
    simpa using this
  obtain ⟨D, hD, hDval⟩ := dep_count (n := n) C k le_rfl W hWlt
  have hf : ∀ x y : Fin n → Bool, (∀ i ∈ D, x i = y i) → f x = f y := by
    intro x y hxy
    rw [← hC x, ← hC y]
    change val C x C.output = val C y C.output
    by_cases ho : C.output < n + k
    · exact hDval x y hxy C.output (Finset.mem_filter.2 ⟨Finset.mem_singleton_self _, ho⟩)
    · rw [val_beyond C x C.output (by omega), val_beyond C y C.output (by omega)]
  have hall : ∀ i : Fin n, i ∈ D := by
    intro i
    by_contra hi
    obtain ⟨x, hx⟩ := hdep i
    apply hx
    apply hf
    intro j hj
    have hji : j ≠ i := fun h => hi (h ▸ hj)
    simp [Function.update_of_ne hji]
  have huniv : (Finset.univ : Finset (Fin n)).card ≤ D.card :=
    Finset.card_le_card (fun i _ => hall i)
  rw [Finset.card_univ, Fintype.card_fin] at huniv
  unfold PEqualNP.MetaComplexity.BinaryCircuit.size at hsize
  omega
