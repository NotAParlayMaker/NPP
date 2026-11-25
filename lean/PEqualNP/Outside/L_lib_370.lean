import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_370

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def mapGate (w : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map w⟩

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) x

theorem simulate (w : ℕ → ℕ) (old new : List Bool) (K : ℕ)
    (read : ∀ (ts : List Bool), ts.length ≤ K → ∀ i,
      (new ++ ts).getD (w i) false = (old ++ ts).getD i false)
    (gs : List Gate) (ts : List Bool) (bound : ts.length + gs.length ≤ K) (o : ℕ) :
    (run (gs.map (mapGate w)) (new ++ ts)).getD (w o) false =
    (run gs (old ++ ts)).getD o false := by
  induction gs generalizing ts with
  | nil => exact read ts (by simpa using bound) o
  | cons g gs ih =>
    let b := g.op.eval (g.inputs.map fun i => (old ++ ts).getD i false)
    have hargs : ((mapGate w g).inputs.map fun i => (new ++ ts).getD i false) =
        g.inputs.map (fun i => (old ++ ts).getD i false) := by
      simp only [mapGate, List.map_map, Function.comp_def]
      exact List.map_congr_left (fun i _ => read ts (by simp at bound; omega) i)
    change (run (gs.map (mapGate w)) ((new ++ ts) ++ [g.op.eval _])).getD (w o) false =
      (run gs ((old ++ ts) ++ [b])).getD o false
    rw [hargs]
    simpa only [List.append_assoc] using ih (ts ++ [b]) (by simp_all; omega)

theorem read_one {n m : ℕ} (u : Fin n) (v : Fin m) (i : ℕ) :
    (oneEach u v).getD i false = decide (i = u.val ∨ i = n + v.val) := by
  unfold oneEach
  by_cases h : i < n
  · rw [List.getD_append _ _ _ _ (by simpa using h)]
    have hne : i ≠ n + v.val := by omega
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem, h, hne, Fin.ext_iff]
  · rw [List.getD_append_right _ _ _ _ (by simp; omega)]
    simp only [List.length_ofFn]
    by_cases h' : i - n < m
    · have hne : i ≠ u.val := by omega
      have he : i - n = v.val ↔ i = n + v.val := by omega
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem, h', hne, Fin.ext_iff, he]
    · rw [List.getD_eq_default _ _ (by simp; omega)]
      have h1 : i ≠ u.val := by omega
      have h2 : i ≠ n + v.val := by omega
      simp [h1,h2]

noncomputable def inputWire {n n' m m' : ℕ} (e : Fin m → Fin n) (f : Fin m' → Fin n')
    (K i : ℕ) : ℕ := by
  classical
  exact if h : ∃ j, (e j).val = i then h.choose.val
    else if h : ∃ j, n + (f j).val = i then m + h.choose.val
    else m + m' + K

noncomputable def wire {n n' m m' : ℕ} (e : Fin m → Fin n) (f : Fin m' → Fin n')
    (K i : ℕ) := if i < n + n' then inputWire e f K i else m + m' + (i - (n + n'))

theorem read_wire {n n' m m' : ℕ} (e : Fin m → Fin n) (f : Fin m' → Fin n')
    (he : Function.Injective e) (hf : Function.Injective f) (K : ℕ) (u : Fin m) (v : Fin m')
    (ts : List Bool) (ht : ts.length ≤ K) (i : ℕ) :
    (oneEach u v ++ ts).getD (wire e f K i) false =
      (oneEach (e u) (f v) ++ ts).getD i false := by
  classical
  have oldLen : (oneEach (e u) (f v)).length = n + n' := by simp [oneEach]
  have newLen : (oneEach u v).length = m + m' := by simp [oneEach]
  unfold wire
  split_ifs with hi
  · rw [List.getD_append _ _ _ _ (show i < (oneEach (e u) (f v)).length by omega), read_one]
    unfold inputWire
    split_ifs with h1 h2
    · have hx := h1.choose_spec
      rw [List.getD_append _ _ _ _ (show h1.choose.val < (oneEach u v).length by omega), read_one]
      have eq : h1.choose.val = u.val ↔ i = (e u).val := by
        rw [← hx]
        exact ⟨fun h => congrArg Fin.val (congrArg e (Fin.ext h)), fun h => congrArg Fin.val (he (Fin.ext h))⟩
      have neq : h1.choose.val ≠ m + v.val := by omega
      have neq' : i ≠ n + (f v).val := by omega
      simp [neq,neq',eq]
    · have hx := h2.choose_spec
      rw [List.getD_append _ _ _ _
        (show m + h2.choose.val < (oneEach u v).length by omega), read_one]
      have eq : h2.choose.val = v.val ↔ i = n + (f v).val := by
        rw [← hx, Nat.add_left_cancel_iff]
        exact ⟨fun h => congrArg Fin.val (congrArg f (Fin.ext h)), fun h => congrArg Fin.val (hf (Fin.ext h))⟩
      have neq : m + h2.choose.val ≠ u.val := by omega
      have neq' : i ≠ (e u).val := fun h => h1 ⟨u,h.symm⟩
      simp [neq,neq',eq]
    · rw [List.getD_eq_default _ _ (by simp [newLen]; omega)]
      have neq : i ≠ (e u).val := fun h => h1 ⟨u,h.symm⟩
      have neq' : i ≠ n + (f v).val := fun h => h2 ⟨v,h.symm⟩
      simp [neq,neq']
  · rw [List.getD_append_right _ _ _ _ (show (oneEach u v).length ≤ _ by omega),
        List.getD_append_right _ _ _ _ (show (oneEach (e u) (f v)).length ≤ i by omega)]
    simp [newLen,oldLen]

end PEqualNP.Outside.L_lib_370

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents PEqualNP.Outside.L_lib_370

theorem PEqualNP.Outside.L_lib_370 : ∀ (n n' m m' s : ℕ) (A : Fin n → Fin n' → Bool) (e : Fin m → Fin n) (f : Fin m' → Fin n'), Function.Injective e → Function.Injective f → PEqualNP.Represents.RepSizeAtMost A s → PEqualNP.Represents.RepSizeAtMost (fun u v => A (e u) (f v)) s := by
  rintro n n' m m' s A e f he hf ⟨C, hm, hs, hA⟩
  let w := wire e f C.size
  refine ⟨⟨C.gates.map (mapGate w), w C.output⟩, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
    simpa [mapGate] using hm g' hg'
  · simpa [Circuit.size] using hs
  · intro u v
    refine Eq.trans ?_ (hA (e u) (f v))
    simpa only [List.append_nil] using simulate w (oneEach (e u) (f v)) (oneEach u v) C.size
      (read_wire e f he hf C.size u v) C.gates [] (by simp [Circuit.size]) C.output
