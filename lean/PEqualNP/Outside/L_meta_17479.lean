import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17479

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm

private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private def run (gs : List Gate) (w : List Bool) : List Bool := gs.foldl step w

private theorem run_append (a b : List Gate) (w : List Bool) :
    run (a ++ b) w = run b (run a w) := by
  simp [run, List.foldl_append]

private theorem run_prefix (gs : List Gate) (w : List Bool) :
    ∃ t : List Bool, run gs w = w ++ t ∧ t.length = gs.length := by
  induction gs generalizing w with
  | nil => exact ⟨[], by simp [run], rfl⟩
  | cons g gs ih =>
    obtain ⟨t, he, hl⟩ := ih (step w g)
    let b := g.op.eval (g.inputs.map fun i => w.getD i false)
    refine ⟨b :: t, ?_, by simp [hl]⟩
    change run gs (step w g) = w ++ b :: t
    rw [he]
    simp [step, b]

private theorem run_length (gs : List Gate) (w : List Bool) :
    (run gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := run_prefix gs w
  simp [ht, hl]

private theorem run_old (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (run gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := run_prefix gs w
  rw [ht, List.getD_append _ _ _ _ hi]

private theorem read_snoc (w : List Bool) (b : Bool) (i : ℕ) :
    (w ++ [b]).getD i false = if i = w.length then b else w.getD i false := by
  by_cases hi : i < w.length
  · rw [List.getD_append _ _ _ _ hi, ite_eq_right (ne_of_lt hi)]
  by_cases he : i = w.length
  · subst i
    simp [List.getD_eq_getElem?_getD]
  · rw [ite_eq_right he, List.getD_eq_default _ _ (by simp; omega),
       List.getD_eq_default _ _ (by omega)]

private theorem prefix_static (gs : List Gate) (hf : ∀ g ∈ gs, 0 ∉ g.inputs)
    (a b : List Bool) (hab : a.length = b.length)
    (eq : ∀ i ≠ 0, a.getD i false = b.getD i false) :
    ∀ i ≠ 0, (run gs a).getD i false = (run gs b).getD i false := by
  induction gs generalizing a b with
  | nil => exact eq
  | cons g gs ih =>
    have hgate : (g.inputs.map fun i => a.getD i false) =
        g.inputs.map fun i => b.getD i false := by
      apply List.map_congr_left
      intro i hi
      exact eq i (fun e => hf g (by simp) (e ▸ hi))
    change ∀ i ≠ 0, (run gs (step a g)).getD i false = (run gs (step b g)).getD i false
    apply ih (fun h hh => hf h (by simp [hh])) _ _
    · simp [step, hab]
    · intro i hi
      simp only [step, read_snoc, hab, hgate, eq i hi]

private def ren (cut i : ℕ) : ℕ :=
  if i = 0 then cut else if i < cut then i else i+1

private def remap (cut : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (ren cut)⟩

private theorem ren_inj (cut : ℕ) : Function.Injective (ren cut) := by
  intro i j hij
  unfold ren at hij
  split_ifs at hij <;> omega

private theorem ren_next {cut i : ℕ} (hp : 0 < cut) (hi : cut ≤ i) :
    ren cut i = i+1 := by
  simp [ren, show i ≠ 0 by omega, Nat.not_lt.mpr hi]

private theorem suffix_map (cut : ℕ) (hcut : 0 < cut)
    (gs : List Gate) (a b : List Bool)
    (hlen : b.length = a.length + 1) (ha : cut ≤ a.length)
    (eq : ∀ i, b.getD (ren cut i) false = a.getD i false) :
    ∀ i, (run (gs.map (remap cut)) b).getD (ren cut i) false = (run gs a).getD i false := by
  induction gs generalizing a b with
  | nil => exact eq
  | cons g gs ih =>
    have map_eq : ((remap cut g).inputs.map fun i => b.getD i false) =
        g.inputs.map fun i => a.getD i false := by
      simp only [remap, List.map_map]
      exact List.map_congr_left fun i _ => eq i
    have next : ren cut a.length = b.length := by
      rw [ren_next hcut ha, hlen]
    change ∀ i, (run (gs.map (remap cut)) (step b (remap cut g))).getD (ren cut i) false =
      (run gs (step a g)).getD i false
    apply ih _ _
    · simp [step, hlen, Nat.add_assoc]
    · simp [step]; omega
    · intro i
      have test : ren cut i = b.length ↔ i = a.length := by
        rw [← next]
        exact (ren_inj cut).eq_iff
      simp only [step, read_snoc, test, (show (remap cut g).op = g.op from rfl), map_eq, eq i]

private theorem update_read (x : Fin 10 → Bool) (b : Bool) (i : ℕ) (hi : i ≠ 0) :
    (List.ofFn x).getD i false = (List.ofFn (Function.update x 0 b)).getD i false := by
  by_cases hb : i < 10
  · have e : (⟨i,hb⟩ : Fin 10) ≠ 0 := fun h => hi (congrArg Fin.val h)
    have hl : i < (List.ofFn x).length := by simpa only [List.length_ofFn] using hb
    have hr : i < (List.ofFn (Function.update x (0 : Fin 10) b)).length := by
      simpa only [List.length_ofFn] using hb
    rw [List.getD_eq_getElem _ _ hl, List.getD_eq_getElem _ _ hr]
    simp only [List.getElem_ofFn, Function.update_of_ne e]
  · have hl : (List.ofFn x).length ≤ i := by simp; omega
    have hr : (List.ofFn (Function.update x (0 : Fin 10) b)).length ≤ i := by simp; omega
    rw [List.getD_eq_default _ _ hl, List.getD_eq_default _ _ hr]

private theorem raw_zero (gs : List Gate) (x : Fin 10 → Bool) :
    (run gs (List.ofFn x)).getD 0 false = x 0 := by
  rw [run_old _ _ _ (by simp)]
  simp [List.getD_eq_getElem?_getD]

private theorem get_bounds (C : Circuit) (hs : IsAO2 10 C) {j : ℕ} {g : Gate}
    (hg : C.gates[j]? = some g) : ∀ v ∈ g.inputs, v < 10+j := by
  have hj := (List.getElem?_eq_some_iff.mp hg).1
  simpa [gateAt, List.getD_eq_getElem?_getD, hg] using hs.2.1 j hj

private theorem splice (C : Circuit) (w : ℕ) (hs : IsAO2 10 C) (hw0 : w ≠ 0)
    (hw : w < 10 + C.size)
    (hn : ∀ (j : ℕ) (g : Gate), 10+j ≤ w → C.gates[j]? = some g → 0 ∉ g.inputs) :
    ∃ D : Circuit, IsAO2 10 D ∧ D.size ≤ C.size+1 ∧
      ∀ x : Fin 10 → Bool,
        circuitFun 10 D x = circuitFun 10 C
          (Function.update x 0 (x 0 || (C.wires (List.ofFn (Function.update x 0 false))).getD w false)) := by
  have hwg : w < 10 + C.gates.length := hw
  let k := w+1-10
  let P := C.gates.take k
  let S := C.gates.drop k
  let cut := 10+k
  have hk : k ≤ C.gates.length := by dsimp [k]; omega
  have hP : P.length = k := by simp [P, Nat.min_eq_left hk]
  have hS : P ++ S = C.gates := List.take_append_drop k C.gates
  have hcut : 0 < cut := by dsimp [cut]; omega
  have hwcut : w < cut := by dsimp [cut,k]; omega
  let G : Gate := ⟨.or,[0,w]⟩
  let D : Circuit := ⟨P ++ G :: S.map (remap cut), ren cut C.output⟩
  refine ⟨D, ?_, ?_, ?_⟩
  · have group (j : ℕ) (g : Gate) (hg : D.gates[j]? = some g) :
        (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2 ∧ ∀ a ∈ g.inputs, a < 10+j := by
      by_cases hj : j < k
      · have hpj : j < P.length := by omega
        have hpc : P[j]? = some g := by
          simpa only [D, List.getElem?_append_left hpj] using hg
        have hgc : C.gates[j]? = some g := by
          rw [← hS, List.getElem?_append_left hpj]
          exact hpc
        exact ⟨hs.1 g (List.mem_of_getElem? hgc),
          hs.2.2 g (List.mem_of_getElem? hgc), get_bounds C hs hgc⟩
      · by_cases he : j = k
        · subst j
          have e : G = g := by
            simpa [D, List.getElem?_append_right (by omega : P.length ≤ k), hP] using hg
          subst g
          refine ⟨Or.inr rfl, rfl, ?_⟩
          intro a ha
          simp only [G, List.mem_cons, List.not_mem_nil, or_false] at ha
          rcases ha with rfl|rfl
          · omega
          · exact hwcut
        · have hpj : P.length ≤ j := by omega
          have hsub : j-P.length=(j-1-P.length)+1 := by omega
          have htail : (S[j-1-P.length]?).map (remap cut) = some g := by
            simpa only [D, List.getElem?_append_right hpj, hsub, List.getElem?_cons_succ,
              List.getElem?_map] using hg
          obtain ⟨g₀, ht, rfl⟩ := Option.map_eq_some_iff.1 htail
          have hgc : C.gates[j-1]? = some g₀ := by
            rw [← hS, List.getElem?_append_right (by omega : P.length ≤ j-1)]
            exact ht
          refine ⟨hs.1 g₀ (List.mem_of_getElem? hgc), ?_, ?_⟩
          · simpa [remap] using hs.2.2 g₀ (List.mem_of_getElem? hgc)
          · intro a ha
            obtain ⟨a₀, h₀, rfl⟩ := List.mem_map.mp (show a ∈ g₀.inputs.map (ren cut) from ha)
            have hlt := get_bounds C hs hgc a₀ h₀
            unfold ren
            dsimp [cut]
            split_ifs <;> omega
    refine ⟨?_, ?_, ?_⟩
    · intro g hg
      obtain ⟨j, hj, e⟩ := List.getElem_of_mem hg
      exact (group j g (List.getElem?_eq_some_iff.2 ⟨hj,e⟩)).1
    · intro j hj
      let g := D.gates[j]
      have hget : D.gates[j]? = some g := List.getElem?_eq_some_iff.2 ⟨hj,rfl⟩
      simpa [gateAt, List.getD_eq_getElem?_getD, hget] using (group j g hget).2.2
    · intro g hg
      obtain ⟨j, hj, e⟩ := List.getElem_of_mem hg
      exact (group j g (List.getElem?_eq_some_iff.2 ⟨hj,e⟩)).2.1
  · have old : P.length + S.length = C.gates.length := by
      simpa using congrArg List.length hS
    simp only [D, Circuit.size, List.length_append, List.length_cons, List.length_map]
    omega
  · intro x
    let t := Function.update x (0 : Fin 10) false
    let b := x 0 || (C.wires (List.ofFn t)).getD w false
    let y := Function.update x (0 : Fin 10) b
    let u := run P (List.ofFn x)
    let v := run P (List.ofFn y)
    have hu : u.length = cut := by simp [u,run_length,hP,cut]
    have hv : v.length = cut := by simp [v,run_length,hP,cut]
    have hnf : ∀ g ∈ P, 0 ∉ g.inputs := by
      intro g hg
      obtain ⟨j,hj,e⟩ := List.getElem_of_mem hg
      have hjk : j < k := by omega
      have hd : C.gates[j]? = some g := by
        rw [← hS, List.getElem?_append_left hj]
        exact List.getElem?_eq_some_iff.2 ⟨hj,e⟩
      apply hn j g (by dsimp [k] at hjk; omega) hd
    have hStatic (c : Bool) (i : ℕ) (hi : i ≠ 0) :
        u.getD i false = (run P (List.ofFn (Function.update x 0 c))).getD i false :=
      prefix_static P hnf _ _ (by simp) (fun j hj => update_read x c j hj) i hi
    have hval : u.getD w false = (C.wires (List.ofFn t)).getD w false := by
      rw [hStatic false w hw0]
      change (run P (List.ofFn t)).getD w false = (run C.gates (List.ofFn t)).getD w false
      rw [← hS, run_append]
      apply (run_old S _ _ _).symm
      simpa only [run_length, List.length_ofFn, hP] using hwcut
    have hup : step u G = u ++ [b] := by
      have zero : u.getD 0 false = x 0 := raw_zero P x
      have pair_or (a c : Bool) : GateOp.or.eval [a,c] = (a || c) := by
        cases a <;> cases c <;> rfl
      change u ++ [GateOp.or.eval ([0,w].map fun i => u.getD i false)] = _
      simp only [List.map_cons, List.map_nil, pair_or, zero, hval, b]
    have hmap : ∀ i, (u ++ [b]).getD (ren cut i) false = v.getD i false := by
      intro i
      by_cases hi : i = 0
      · subst i
        simp only [ren, ite_true, read_snoc, hu]
        change b = (run P (List.ofFn y)).getD 0 false
        rw [raw_zero]
        simp [y]
      · by_cases il : i < cut
        · rw [show ren cut i = i by simp [ren,hi,il],
            List.getD_append _ _ _ _ (by omega)]
          exact hStatic b i hi
        · rw [ren_next hcut (by omega),
            List.getD_eq_default _ _ (by simp [hu]; omega),
            List.getD_eq_default _ _ (by omega)]
    have hh := suffix_map cut hcut S v (u++[b]) (by simp [hu,hv]) (by omega) hmap C.output
    change (run D.gates (List.ofFn x)).getD (ren cut C.output) false =
      (run C.gates (List.ofFn y)).getD C.output false
    have left : run D.gates (List.ofFn x) = run (S.map (remap cut)) (u ++ [b]) := by
      change run (P ++ G :: S.map (remap cut)) (List.ofFn x) = _
      rw [run_append]
      change run (S.map (remap cut)) (step u G) = _
      rw [hup]
    rw [left, ← hS, run_append]
    exact hh

end PEqualNP.Outside.L_meta_17479

open PEqualNP.Outside.L_meta_17479 in

theorem PEqualNP.Outside.L_meta_17479 :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : ℕ), PEqualNP.TopForm.IsAO2 (10 : ℕ) x1 → x2 ≠ (0 : ℕ) → x2 < (10 : ℕ) + x1.size → (∀ (x6 : ℕ) (x7 : PEqualNP.CircuitLowerBounds.Gate), (10 : ℕ) + x6 ≤ x2 → x1.gates[x6]? = Option.some x7 → (0 : ℕ) ∉ x7.inputs) → ∃ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (10 : ℕ) x7 ∧ x7.size ≤ x1.size + (1 : ℕ) ∧ ∀ (x8 : Fin (10 : ℕ) → Bool), PEqualNP.MetaComplexity.circuitFun (10 : ℕ) x7 x8 = PEqualNP.MetaComplexity.circuitFun (10 : ℕ) x1 (Function.update x8 (0 : Fin (10 : ℕ)) (x8 (0 : Fin (10 : ℕ)) || (x1.wires (List.ofFn (Function.update x8 (0 : Fin (10 : ℕ)) Bool.false))).getD x2 Bool.false)) := by
  exact splice

