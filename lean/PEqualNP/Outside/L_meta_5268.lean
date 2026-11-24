import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5268

open PEqualNP.CircuitLowerBounds

def ren (ρ : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map ρ⟩

lemma getD_snoc {β : Type} (d : List β) (a dflt : β) (i : ℕ) :
    (d ++ [a]).getD i dflt =
      if i < d.length then d.getD i dflt else if i = d.length then a else dflt := by
  simp only [List.getD_eq_getElem?_getD]
  split_ifs with h1 h2
  · rw [List.getElem?_append_left h1]
  · subst h2; simp
  · rw [List.getElem?_eq_none (by simp; omega)]; rfl

lemma run_ren {β : Type} (F : Gate → List β → β) (H : GateOp → List β → β) (dflt : β)
    (hF : ∀ g d, F g d = H g.op (g.inputs.map fun i => d.getD i dflt))
    (ρ : ℕ → ℕ) (n : ℕ) (h1 : ∀ w, n ≤ w → ρ w = w) (h2 : ∀ w < n, ρ w < n) :
    ∀ (gs : List Gate) (d1 d2 : List β), d1.length = d2.length → n ≤ d1.length →
      (∀ w, d2.getD (ρ w) dflt = d1.getD w dflt) →
      ∀ w, ((gs.map (ren ρ)).foldl (fun d g => d ++ [F g d]) d2).getD (ρ w) dflt =
        (gs.foldl (fun d g => d ++ [F g d]) d1).getD w dflt := by
  intro gs
  induction gs with
  | nil => intro d1 d2 _ _ h w; exact h w
  | cons g gs ih =>
    intro d1 d2 hl hn h
    simp only [List.map_cons, List.foldl_cons]
    apply ih
    · simp [hl]
    · simp; omega
    · intro w
      have hv : F (ren ρ g) d2 = F g d1 := by
        rw [hF, hF]
        simp only [ren, List.map_map]
        congr 1
        apply List.map_congr_left
        intro i _
        exact h i
      rw [getD_snoc, getD_snoc, hv, ← hl]
      by_cases hw : w < d1.length
      · have hr : ρ w < d1.length := by
          by_cases hwn : w < n
          · have := h2 w hwn; omega
          · rw [h1 w (by omega)]; exact hw
        rw [if_pos hr, if_pos hw, h w]
      · rw [h1 w (by omega), if_neg hw, if_neg hw]

def rho (σ τ : Equiv.Perm (Fin 7)) (i : ℕ) : ℕ :=
  if h : i < 7 then ((σ ⟨i, h⟩ : Fin 7) : ℕ)
  else if h2 : i < 14 then 7 + ((τ ⟨i - 7, by omega⟩ : Fin 7) : ℕ) else i

lemma rho_big (σ τ : Equiv.Perm (Fin 7)) (w : ℕ) (hw : 14 ≤ w) : rho σ τ w = w := by
  unfold rho; rw [dif_neg (by omega), dif_neg (by omega)]

lemma rho_small (σ τ : Equiv.Perm (Fin 7)) (w : ℕ) (hw : w < 14) : rho σ τ w < 14 := by
  unfold rho
  split_ifs
  · have := (σ ⟨w, by omega⟩).isLt; omega
  · have := (τ ⟨w - 7, by omega⟩).isLt; omega

lemma rho_pt (σ τ : Equiv.Perm (Fin 7)) (p : Fin 7) : rho σ τ p = ((σ p : Fin 7) : ℕ) := by
  unfold rho; rw [dif_pos p.isLt]

lemma rho_ln (σ τ : Equiv.Perm (Fin 7)) (l : Fin 7) :
    rho σ τ (7 + l) = 7 + ((τ l : Fin 7) : ℕ) := by
  have := l.isLt
  unfold rho; rw [dif_neg (by omega), dif_pos (by omega)]
  congr 3; ext; simp

lemma rho_inj (σ τ : Equiv.Perm (Fin 7)) (i j : ℕ) (h : rho σ τ i = rho σ τ j) : i = j := by
  unfold rho at h
  split_ifs at h with a b c d e f g k
  all_goals first
    | omega
    | (have := Fin.ext h; have := σ.injective this; simp [Fin.ext_iff] at this; omega)
    | (have := (σ ⟨i, by omega⟩).isLt; have := (τ ⟨j - 7, by omega⟩).isLt; omega)
    | (have := (τ ⟨i - 7, by omega⟩).isLt; have := (σ ⟨j, by omega⟩).isLt; omega)
    | (have h' : (τ ⟨i - 7, by omega⟩) = τ ⟨j - 7, by omega⟩ := Fin.ext (by omega)
       have := τ.injective h'; simp [Fin.ext_iff] at this; omega)
    | (have := (σ ⟨i, by omega⟩).isLt; omega)
    | (have := (σ ⟨j, by omega⟩).isLt; omega)
    | (have := (τ ⟨i - 7, by omega⟩).isLt; omega)
    | (have := (τ ⟨j - 7, by omega⟩).isLt; omega)

lemma ofFn_getD (f : Fin 14 → Bool) (i : ℕ) :
    (List.ofFn f).getD i false = if h : i < 14 then f ⟨i, h⟩ else false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  by_cases h : i < 14
  · rw [dif_pos h, dif_pos h]; rfl
  · rw [dif_neg h, dif_neg h]; rfl

def ren9 (σ τ : Equiv.Perm (Fin 7)) (C : Circuit) : Circuit :=
  ⟨C.gates.map (ren (rho σ τ)), rho σ τ C.output⟩

lemma wires_ren (σ τ : Equiv.Perm (Fin 7)) (C : Circuit) (x : Fin 14 → Bool) (w : ℕ) :
    ((ren9 σ τ C).wires (List.ofFn x)).getD (rho σ τ w) false =
      (C.wires (List.ofFn fun i : Fin 14 =>
        x ⟨rho σ τ i, rho_small σ τ i i.isLt⟩)).getD w false := by
  apply run_ren (fun g w => g.op.eval (g.inputs.map fun i => w.getD i false)) GateOp.eval false
    (fun _ _ => rfl) (rho σ τ) 14 (rho_big σ τ) (rho_small σ τ)
  · simp
  · simp
  · intro v
    rw [ofFn_getD, ofFn_getD]
    by_cases hv : v < 14
    · rw [dif_pos (rho_small σ τ v hv), dif_pos hv]
    · rw [rho_big σ τ v (by omega)]; simp [hv]

def Hd (op : GateOp) (l : List ℕ) : ℕ :=
  @ite _ (op = GateOp.and) (lineDegreeGateOpDecEq op GateOp.and) l.sum (l.foldr max 0)

lemma deg_ren (σ τ : Equiv.Perm (Fin 7)) (C : Circuit) (m w : ℕ) :
    ((ren9 σ τ C).lineDegrees 14 {rho σ τ m}).getD (rho σ τ w) 0 =
      (C.lineDegrees 14 {m}).getD w 0 := by
  apply run_ren (fun g d => g.lineDegree d) Hd 0 (fun _ _ => rfl) (rho σ τ) 14
    (rho_big σ τ) (rho_small σ τ)
  · simp
  · simp
  · intro v
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
    by_cases hv : v < 14
    · rw [List.getElem?_range (rho_small σ τ v hv), List.getElem?_range hv]
      have : rho σ τ v = rho σ τ m ↔ v = m := ⟨rho_inj σ τ v m, fun h => h ▸ rfl⟩
      simp [this]
    · rw [rho_big σ τ v (by omega), List.getElem?_eq_none (by simp; omega)]
      rfl

lemma filt (σ τ : Equiv.Perm (Fin 7)) (L : List ℕ) :
    (L.map (rho σ τ)).filter (fun x => decide (14 ≤ x)) = L.filter (fun x => decide (14 ≤ x)) := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    by_cases h : 14 ≤ a
    · simp [List.filter_cons, h, rho_big σ τ a h, ih]
    · have : ¬ 14 ≤ rho σ τ a := by have := rho_small σ τ a (by omega); omega
      simp [List.filter_cons, h, this, ih]

lemma fmap (σ τ : Equiv.Perm (Fin 7)) (gs : List Gate) :
    List.flatMap Gate.inputs (gs.map (ren (rho σ τ))) = (List.flatMap Gate.inputs gs).map (rho σ τ) := by
  induction gs with
  | nil => rfl
  | cons g gs ih => simp [List.flatMap_cons, ren, ih]

end PEqualNP.Outside.L_meta_5268

open PEqualNP.Outside.L_meta_5268 in
theorem PEqualNP.Outside.L_meta_5268 : have x1 : Fin (7 : ℕ) → Fin (7 : ℕ) → Prop := fun (x1 x2 : Fin (7 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (7 : ℕ)) ∨ x1 = x2 + (3 : Fin (7 : ℕ)); have x2 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) => x2.size ≤ (27 : ℕ) ∧ (∀ (x3 : ℕ) (x4 : PEqualNP.CircuitLowerBounds.Gate), x2.gates[x3]? = Option.some x4 → (x4.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x4.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x6 : ℕ) (x7 : ℕ), x4.inputs = [x6, x7] ∧ x6 ≠ x7 ∧ x6 < (14 : ℕ) + x3 ∧ x7 < (14 : ℕ) + x3) ∧ ∀ (x3 : Fin (14 : ℕ) → Bool), x2.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (7 : ℕ)) (x5 : Fin (7 : ℕ)), x1 x4 x5 ∧ x3 (Fin.castAdd (7 : ℕ) x4) = Bool.true ∧ x3 (Fin.natAdd (7 : ℕ) x5) = Bool.true; have x3 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) => (List.filter (fun (x4 : ℕ) => Decidable.decide ((14 : ℕ) ≤ x4)) (x3.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x3.gates)).Nodup; ∀ (x4 x5 : Equiv.Perm (Fin (7 : ℕ))), (∀ (x6 x7 : Fin (7 : ℕ)), x1 (x4 x6) (x5 x7) ↔ x1 x6 x7) → ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), x2 x7 → ∃ (x9 : PEqualNP.CircuitLowerBounds.Circuit), x2 x9 ∧ (x3 x9 ↔ x3 x7) ∧ (∀ (x10 : Fin (7 : ℕ)), x9.lineDeg (14 : ℕ) {↑(x4 x10)} = x7.lineDeg (14 : ℕ) {↑x10}) ∧ ∀ (x10 : Fin (7 : ℕ)), x9.lineDeg (14 : ℕ) {(7 : ℕ) + ↑(x5 x10)} = x7.lineDeg (14 : ℕ) {(7 : ℕ) + ↑x10} := by
  intro I P Q σ τ hI C hC
  have key : ∀ x : Fin 14 → Bool, (ren9 σ τ C).eval (List.ofFn x) =
      C.eval (List.ofFn fun i : Fin 14 => x ⟨rho σ τ i, rho_small σ τ i i.isLt⟩) :=
    fun x => wires_ren σ τ C x C.output
  obtain ⟨hsz, hg, hev⟩ := hC
  refine ⟨ren9 σ τ C, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · simpa [ren9, PEqualNP.CircuitLowerBounds.Circuit.size] using hsz
  · intro j g hj
    simp only [ren9, List.getElem?_map] at hj
    cases hj0 : C.gates[j]? with
    | none => rw [hj0] at hj; simp at hj
    | some g0 =>
      rw [hj0] at hj
      simp only [Option.map_some, Option.some.injEq] at hj
      subst hj
      obtain ⟨hop, a, b, hin, hab, ha, hb⟩ := hg j g0 hj0
      refine ⟨hop, rho σ τ a, rho σ τ b, by simp [ren, hin], fun h => hab (rho_inj σ τ a b h), ?_, ?_⟩
      · by_cases h : a < 14
        · have := rho_small σ τ a h; omega
        · rw [rho_big σ τ a (by omega)]; exact ha
      · by_cases h : b < 14
        · have := rho_small σ τ b h; omega
        · rw [rho_big σ τ b (by omega)]; exact hb
  · intro x
    rw [key, hev]
    constructor
    · rintro ⟨p, l, hpl, hp, hl⟩
      refine ⟨σ p, τ l, (hI p l).mpr hpl, ?_, ?_⟩
      · convert hp using 2
        ext; simp [rho_pt]
      · convert hl using 2
        ext
        simp only [Fin.val_mk, Fin.coe_natAdd, rho_ln]
    · rintro ⟨p, l, hpl, hp, hl⟩
      refine ⟨σ.symm p, τ.symm l, (hI _ _).mp (by simpa using hpl), ?_, ?_⟩
      · convert hp using 2
        ext; simp [rho_pt]
      · convert hl using 2
        ext
        simp only [Fin.val_mk, Fin.coe_natAdd, rho_ln, Equiv.apply_symm_apply]
  · show (List.filter _ ((rho σ τ C.output) :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs
        (C.gates.map (ren (rho σ τ))))).Nodup ↔ _
    rw [fmap, ← List.map_cons, filt]
  · intro p
    unfold PEqualNP.CircuitLowerBounds.Circuit.lineDeg
    rw [← rho_pt σ τ p]
    exact deg_ren σ τ C p C.output
  · intro l
    unfold PEqualNP.CircuitLowerBounds.Circuit.lineDeg
    rw [← rho_ln σ τ l]
    exact deg_ren σ τ C (7 + l) C.output
