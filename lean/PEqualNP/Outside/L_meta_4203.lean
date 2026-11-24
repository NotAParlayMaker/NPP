import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4203

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def permWire (n : ℕ) (σ : Equiv.Perm (Fin n)) (w : ℕ) : ℕ :=
  if h : w < n then (σ ⟨w, h⟩).val else w

def permGate (n : ℕ) (σ : Equiv.Perm (Fin n)) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (permWire n σ)⟩

def permCircuit (n : ℕ) (σ : Equiv.Perm (Fin n)) (C : Circuit) : Circuit :=
  ⟨C.gates.map (permGate n σ), permWire n σ C.output⟩

lemma permWire_fin (n : ℕ) (σ : Equiv.Perm (Fin n)) (v : Fin n) :
    permWire n σ v.val = (σ v).val := by
  simp [permWire, v.isLt]

lemma permWire_ge (n : ℕ) (σ : Equiv.Perm (Fin n)) (w : ℕ) (hw : n ≤ w) :
    permWire n σ w = w := by
  have h : ¬ w < n := by omega
  simp [permWire, h]

lemma permWire_lt_iff (n : ℕ) (σ : Equiv.Perm (Fin n)) (w : ℕ) :
    permWire n σ w < n ↔ w < n := by
  unfold permWire
  split_ifs with h
  · exact ⟨fun _ => h, fun _ => (σ ⟨w, h⟩).isLt⟩
  · exact ⟨fun h' => absurd h' h, fun h' => absurd h' h⟩

lemma permWire_injective (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    Function.Injective (permWire n σ) := by
  intro a b hab
  by_cases ha : a < n <;> by_cases hb : b < n
  · simp only [permWire, ha, hb, ↓reduceDIte] at hab
    have hfin : σ ⟨a, ha⟩ = σ ⟨b, hb⟩ := Fin.ext hab
    exact congrArg Fin.val (σ.injective hfin)
  · simp only [permWire, ha, hb, ↓reduceDIte] at hab
    have := (σ ⟨a, ha⟩).isLt; omega
  · simp only [permWire, ha, hb, ↓reduceDIte] at hab
    have := (σ ⟨b, hb⟩).isLt; omega
  · simp only [permWire, ha, hb, ↓reduceDIte] at hab
    exact hab

lemma permCircuit_size (n : ℕ) (σ : Equiv.Perm (Fin n)) (C : Circuit) :
    (permCircuit n σ C).size = C.size := by
  simp [permCircuit, Circuit.size]

lemma permCircuit_fanInTwo (n : ℕ) (σ : Equiv.Perm (Fin n)) (C : Circuit)
    (h : FanInTwo C) : FanInTwo (permCircuit n σ C) := by
  intro g' hg'
  simp only [permCircuit, List.mem_map] at hg'
  obtain ⟨g, hg, rfl⟩ := hg'
  obtain ⟨hop, hlen⟩ := h g hg
  exact ⟨hop, by simp [permGate, hlen]⟩

lemma foldl_wires_perm (n : ℕ) (σ : Equiv.Perm (Fin n)) (gs : List Gate)
    (w1 w2 : List Bool)
    (hlen : w1.length = w2.length) (hn : n ≤ w1.length)
    (hmatch : ∀ u, u < w1.length → w1.getD (permWire n σ u) false = w2.getD u false) :
    let step : List Bool → Gate → List Bool := fun w g =>
      w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
    let r1 := (gs.map (permGate n σ)).foldl step w1
    let r2 := gs.foldl step w2
    r1.length = r2.length ∧
    (∀ u, r1.getD (permWire n σ u) false = r2.getD u false) := by
  induction gs generalizing w1 w2 with
  | nil =>
    simp only [List.map_nil, List.foldl_nil]
    refine ⟨hlen, fun u => ?_⟩
    by_cases hu : u < w1.length
    · exact hmatch u hu
    · have hu_ge_n : n ≤ u := by omega
      have hpw : permWire n σ u = u := permWire_ge n σ u hu_ge_n
      rw [hpw, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]
  | cons g gs ih =>
    simp only [List.map_cons, List.foldl_cons]
    have hinputs : (permGate n σ g).inputs.map (fun i => w1.getD i false) =
        g.inputs.map (fun i => w2.getD i false) := by
      simp only [permGate, List.map_map]
      refine List.map_congr_left fun u _ => ?_
      change w1.getD (permWire n σ u) false = w2.getD u false
      by_cases hu : u < w1.length
      · exact hmatch u hu
      · have hu_ge_n : n ≤ u := by omega
        rw [permWire_ge n σ u hu_ge_n, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
          List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]
    have hval : (permGate n σ g).op.eval ((permGate n σ g).inputs.map fun i => w1.getD i false) =
        g.op.eval (g.inputs.map fun i => w2.getD i false) := by
      rw [hinputs]; rfl
    refine ih _ _ (by simp [hlen]) (by simp; omega) ?_
    intro u hu
    simp only [List.length_append, List.length_singleton] at hu
    by_cases hult : u < w1.length
    · have hpw_lt : permWire n σ u < w1.length := by
        unfold permWire
        split_ifs with h
        · have := (σ ⟨u, h⟩).isLt; omega
        · exact hult
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hpw_lt,
        List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega)]
      simpa only [List.getD_eq_getElem?_getD] using hmatch u hult
    · have hueq : u = w1.length := by omega
      subst hueq
      rw [permWire_ge n σ w1.length hn, List.getD_eq_getElem?_getD,
        List.getElem?_append_right le_rfl, Nat.sub_self,
        List.getD_eq_getElem?_getD, hlen, List.getElem?_append_right le_rfl, Nat.sub_self]
      simpa only [List.getElem?_cons_zero, Option.getD_some] using hval

lemma permCircuit_eval (n : ℕ) (σ : Equiv.Perm (Fin n)) (C : Circuit) (x : Fin n → Bool) :
    circuitFun n (permCircuit n σ C) x = circuitFun n C (x ∘ σ) := by
  simp only [circuitFun, Circuit.eval, Circuit.wires, permCircuit]
  have h := foldl_wires_perm n σ C.gates (List.ofFn x) (List.ofFn (x ∘ σ))
    (by simp) (by simp) (by
      intro u hu
      simp only [List.length_ofFn] at hu
      rw [permWire_fin n σ ⟨u, hu⟩, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
      simp [hu, (σ ⟨u, hu⟩).isLt])
  exact h.2 C.output

lemma permCircuit_isMinimal (n : ℕ) (σ : Equiv.Perm (Fin n)) (C : Circuit)
    (hmin : IsMinimalCircuit n C) : IsMinimalCircuit n (permCircuit n σ C) := by
  refine ⟨permCircuit_fanInTwo n σ C hmin.1, fun D hDf hDeq => ?_⟩
  let D' := permCircuit n σ.symm D
  have hD'f : FanInTwo D' := permCircuit_fanInTwo n σ.symm D hDf
  have hD'eq : circuitFun n D' = circuitFun n C := by
    funext x
    rw [permCircuit_eval n σ.symm D x]
    have h1 := congrFun hDeq (x ∘ σ.symm)
    rw [h1, permCircuit_eval n σ C (x ∘ σ.symm)]
    congr 1
    funext i
    simp
  have hle := hmin.2 D' hD'f hD'eq
  rw [permCircuit_size n σ C]
  rw [permCircuit_size n σ.symm D] at hle
  exact hle

end PEqualNP.Outside.L_meta_4203

theorem PEqualNP.Outside.L_meta_4203 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Equiv.Perm (Fin x1)),   ∃ (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : Fin x2.size ≃ Fin x4.size),     x4.size = x2.size ∧       (PEqualNP.MetaComplexity.IsMinimalCircuit x1 x2 → PEqualNP.MetaComplexity.IsMinimalCircuit x1 x4) ∧         (∀ (x6 : Fin x1 → Bool), PEqualNP.MetaComplexity.circuitFun x1 x4 x6 = PEqualNP.MetaComplexity.circuitFun x1 x2 (x6 ∘ ⇑x3)) ∧           ∀ (x6 : Fin x2.size),             have x7 : PEqualNP.CircuitLowerBounds.Gate := x2.gates.get x6;             have x8 : PEqualNP.CircuitLowerBounds.Gate := x4.gates.get (x5 x6);             x8.op = x7.op ∧ x8.inputs.length = x7.inputs.length ∧ (x7.inputs.Nodup → x8.inputs.Nodup) ∧ ((∀ x9 ∈ x7.inputs, x9 < x1 + ↑x6) → ∀ x10 ∈ x8.inputs, x10 < x1 + ↑(x5 x6)) ∧ ∀ (x9 : Fin x1), ↑(x3 x9) ∈ x8.inputs ↔ ↑x9 ∈ x7.inputs := by
  intro n C σ
  let C' := PEqualNP.Outside.L_meta_4203.permCircuit n σ C
  have hsz : C'.size = C.size := PEqualNP.Outside.L_meta_4203.permCircuit_size n σ C
  let e : Fin C.size ≃ Fin C'.size := finCongr hsz.symm
  refine ⟨C', e, hsz, PEqualNP.Outside.L_meta_4203.permCircuit_isMinimal n σ C,
    PEqualNP.Outside.L_meta_4203.permCircuit_eval n σ C, ?_⟩
  intro i
  have hget : C'.gates.get (e i) = PEqualNP.Outside.L_meta_4203.permGate n σ (C.gates.get i) := by
    change (C.gates.map (PEqualNP.Outside.L_meta_4203.permGate n σ))[i.val]'(by simp [PEqualNP.CircuitLowerBounds.Circuit.size]; exact i.isLt) =
      PEqualNP.Outside.L_meta_4203.permGate n σ (C.gates[i.val]'i.isLt)
    exact List.getElem_map _
  dsimp only
  rw [hget]
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩
  · simp [PEqualNP.Outside.L_meta_4203.permGate]
  · intro hnd
    exact hnd.map (PEqualNP.Outside.L_meta_4203.permWire_injective n σ)
  · intro hlt w' hw'
    simp only [PEqualNP.Outside.L_meta_4203.permGate, List.mem_map] at hw'
    obtain ⟨w, hw, rfl⟩ := hw'
    have h1 := hlt w hw
    have heval : (e i).val = i.val := rfl
    rw [heval]
    unfold PEqualNP.Outside.L_meta_4203.permWire
    split_ifs with hwn
    · have := (σ ⟨w, hwn⟩).isLt; omega
    · exact h1
  · intro v
    simp only [PEqualNP.Outside.L_meta_4203.permGate, List.mem_map]
    constructor
    · rintro ⟨w, hw, hweq⟩
      rw [← PEqualNP.Outside.L_meta_4203.permWire_fin n σ v] at hweq
      have hEq := PEqualNP.Outside.L_meta_4203.permWire_injective n σ hweq
      rwa [← hEq]
    · intro hv
      exact ⟨v.val, hv, PEqualNP.Outside.L_meta_4203.permWire_fin n σ v⟩
