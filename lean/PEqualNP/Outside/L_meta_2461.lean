import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2461_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.EdgeOwnership

local instance : DecidableEq GateOp := gateOpDecEq

/-! ## Part 1: Explicit projective plane PG(2, 211) -/

abbrev q0 : ℕ := 211
abbrev N0 : ℕ := q0 ^ 2 + q0 + 1

instance : Fact (Nat.Prime q0) := ⟨by norm_num⟩

abbrev Pt := (ZMod q0 × ZMod q0) ⊕ ZMod q0 ⊕ Unit

def vec : Pt → ZMod q0 × ZMod q0 × ZMod q0
  | Sum.inl (a, b) => (1, a, b)
  | Sum.inr (Sum.inl b) => (0, 1, b)
  | Sum.inr (Sum.inr ()) => (0, 0, 1)

def dot (u v : ZMod q0 × ZMod q0 × ZMod q0) : ZMod q0 :=
  u.1 * v.1 + u.2.1 * v.2.1 + u.2.2 * v.2.2

def incPt (u v : Pt) : Prop := dot (vec u) (vec v) = 0

instance : DecidableRel incPt := fun u v => inferInstanceAs (Decidable (dot (vec u) (vec v) = 0))

def normVec (x y z : ZMod q0) : Pt :=
  if x ≠ 0 then Sum.inl (x⁻¹ * y, x⁻¹ * z)
  else if y ≠ 0 then Sum.inr (Sum.inl (y⁻¹ * z))
  else Sum.inr (Sum.inr ())

lemma vec_ne_zero (u : Pt) : vec u ≠ (0, 0, 0) := by
  rcases u with ⟨a, b⟩ | b | ⟨⟩ <;> simp [vec]

lemma vec_normVec {x y z : ZMod q0} (hne : (x, y, z) ≠ (0, 0, 0)) :
    ∃ c : ZMod q0, c ≠ 0 ∧ vec (normVec x y z) = (c * x, c * y, c * z) := by
  by_cases hx : x ≠ 0
  · refine ⟨x⁻¹, inv_ne_zero hx, ?_⟩
    simp [normVec, hx, vec]
  · push Not at hx
    by_cases hy : y ≠ 0
    · refine ⟨y⁻¹, inv_ne_zero hy, ?_⟩
      simp [normVec, hx, hy, vec]
    · push Not at hy
      have hz : z ≠ 0 := by
        intro hz
        exact hne (by simp [hx, hy, hz])
      refine ⟨z⁻¹, inv_ne_zero hz, ?_⟩
      simp [normVec, hx, hy, vec, inv_mul_cancel₀ hz]

lemma eq_of_scale {u v : Pt} {c : ZMod q0} (hc : c ≠ 0)
    (h : vec u = (c * (vec v).1, c * (vec v).2.1, c * (vec v).2.2)) : u = v := by
  rcases u with ⟨a1, b1⟩ | b1 | ⟨⟩ <;> rcases v with ⟨a2, b2⟩ | b2 | ⟨⟩ <;>
    simp only [vec, Prod.mk.injEq, mul_one, mul_zero] at h
  · rcases h with ⟨h1, h2, h3⟩
    have hc1 : c = 1 := h1.symm
    subst hc1
    simp at h2 h3
    simp [h2, h3]
  · exact absurd h.1 one_ne_zero
  · exact absurd h.1 one_ne_zero
  · exact absurd h.1.symm hc
  · rcases h with ⟨_, h2, h3⟩
    have hc1 : c = 1 := h2.symm
    subst hc1
    simp at h3
    simp [h3]
  · exact absurd h.2.1 one_ne_zero
  · exact absurd h.1.symm hc
  · exact absurd h.2.1.symm hc
  · rfl

lemma unique_line_Pt (u v : Pt) (huv : u ≠ v) : ∃! l : Pt, incPt u l ∧ incPt v l := by
  set x1 := (vec u).1
  set y1 := (vec u).2.1
  set z1 := (vec u).2.2
  set x2 := (vec v).1
  set y2 := (vec v).2.1
  set z2 := (vec v).2.2
  set cx := y1 * z2 - z1 * y2
  set cy := z1 * x2 - x1 * z2
  set cz := x1 * y2 - y1 * x2
  have hcne : (cx, cy, cz) ≠ (0, 0, 0) := by
    intro h0
    simp only [Prod.mk.injEq] at h0
    rcases h0 with ⟨hcx, hcy, hcz⟩
    apply huv
    rcases u with ⟨a1, b1⟩ | b1 | ⟨⟩ <;> rcases v with ⟨a2, b2⟩ | b2 | ⟨⟩ <;>
      simp only [x1, y1, z1, x2, y2, z2, cx, cy, cz, vec] at hcx hcy hcz
    · have ha : a1 = a2 := by linear_combination -hcz
      have hb : b1 = b2 := by linear_combination hcy
      simp [ha, hb]
    · simp at hcz
    · simp at hcy
    · simp at hcz
    · have hb : b1 = b2 := by linear_combination -hcx
      simp [hb]
    · simp at hcx
    · simp at hcy
    · simp at hcx
    · rfl
  obtain ⟨c0, hc0, hvec0⟩ := vec_normVec hcne
  set l0 := normVec cx cy cz
  refine ⟨l0, ⟨?_, ?_⟩, ?_⟩
  · unfold incPt dot
    rw [hvec0]
    simp only [x1, y1, z1, x2, y2, z2, cx, cy, cz]
    ring
  · unfold incPt dot
    rw [hvec0]
    simp only [x1, y1, z1, x2, y2, z2, cx, cy, cz]
    ring
  · intro l ⟨hl1, hl2⟩
    unfold incPt dot at hl1 hl2
    set lx := (vec l).1
    set ly := (vec l).2.1
    set lz := (vec l).2.2
    have h1 : x1 * lx + y1 * ly + z1 * lz = 0 := hl1
    have h2 : x2 * lx + y2 * ly + z2 * lz = 0 := hl2
    have hxy : cx * ly = cy * lx := by
      have : z2 * (x1 * lx + y1 * ly + z1 * lz) - z1 * (x2 * lx + y2 * ly + z2 * lz) = 0 := by
        rw [h1, h2]; ring
      linear_combination this
    have hxz : cz * lx = cx * lz := by
      have : y2 * (x1 * lx + y1 * ly + z1 * lz) - y1 * (x2 * lx + y2 * ly + z2 * lz) = 0 := by
        rw [h1, h2]; ring
      linear_combination this
    have hyz : cy * lz = cz * ly := by
      have : x2 * (x1 * lx + y1 * ly + z1 * lz) - x1 * (x2 * lx + y2 * ly + z2 * lz) = 0 := by
        rw [h1, h2]; ring
      linear_combination this
    have hprop : ∃ d : ZMod q0, d ≠ 0 ∧ (lx, ly, lz) = (d * cx, d * cy, d * cz) := by
      by_cases hcx : cx ≠ 0
      · have hd : lx * cx⁻¹ ≠ 0 := by
          intro h0
          have hlx0 : lx = 0 := by
            have := congrArg (· * cx) h0
            simp [inv_mul_cancel_right₀ hcx] at this
            exact this
          have hly0 : ly = 0 := by
            have : cx * ly = 0 := by rw [hxy, hlx0, mul_zero]
            exact (mul_eq_zero.mp this).resolve_left hcx
          have hlz0 : lz = 0 := by
            have : cx * lz = 0 := by rw [← hxz, hlx0, mul_zero]
            exact (mul_eq_zero.mp this).resolve_left hcx
          exact vec_ne_zero l (Prod.ext hlx0 (Prod.ext hly0 hlz0))
        refine ⟨lx * cx⁻¹, hd, Prod.ext ?_ (Prod.ext ?_ ?_)⟩
        · rw [inv_mul_cancel_right₀ hcx]
        · have : lx * cx⁻¹ * cy * cx = ly * cx := by
            calc lx * cx⁻¹ * cy * cx = (lx * cy) * (cx⁻¹ * cx) := by ring
              _ = (cy * lx) * 1 := by rw [inv_mul_cancel₀ hcx]; ring
              _ = cx * ly := by rw [← hxy]; ring
              _ = ly * cx := by ring
          exact mul_right_cancel₀ hcx this.symm
        · have : lx * cx⁻¹ * cz * cx = lz * cx := by
            calc lx * cx⁻¹ * cz * cx = (cz * lx) * (cx⁻¹ * cx) := by ring
              _ = (cx * lz) * 1 := by rw [hxz, inv_mul_cancel₀ hcx]
              _ = lz * cx := by ring
          exact mul_right_cancel₀ hcx this.symm
      · push Not at hcx
        by_cases hcy : cy ≠ 0
        · have hlx0 : lx = 0 := by
            have : cy * lx = 0 := by rw [← hxy, hcx, zero_mul]
            exact (mul_eq_zero.mp this).resolve_left hcy
          have hd : ly * cy⁻¹ ≠ 0 := by
            intro h0
            have hly0 : ly = 0 := by
              have := congrArg (· * cy) h0
              simp [inv_mul_cancel_right₀ hcy] at this
              exact this
            have hlz0 : lz = 0 := by
              have : cy * lz = 0 := by rw [hyz, hly0, mul_zero]
              exact (mul_eq_zero.mp this).resolve_left hcy
            exact vec_ne_zero l (Prod.ext hlx0 (Prod.ext hly0 hlz0))
          refine ⟨ly * cy⁻¹, hd, Prod.ext ?_ (Prod.ext ?_ ?_)⟩
          · simp [hlx0, hcx]
          · rw [inv_mul_cancel_right₀ hcy]
          · have : ly * cy⁻¹ * cz * cy = lz * cy := by
              calc ly * cy⁻¹ * cz * cy = (cz * ly) * (cy⁻¹ * cy) := by ring
                _ = (cy * lz) * 1 := by rw [← hyz, inv_mul_cancel₀ hcy]
                _ = lz * cy := by ring
            exact mul_right_cancel₀ hcy this.symm
        · push Not at hcy
          have hcz : cz ≠ 0 := by
            intro hcz
            exact hcne (by simp [hcx, hcy, hcz])
          have hlx0 : lx = 0 := by
            have : cz * lx = 0 := by rw [hxz, hcx, zero_mul]
            exact (mul_eq_zero.mp this).resolve_left hcz
          have hly0 : ly = 0 := by
            have : cz * ly = 0 := by rw [← hyz, hcy, zero_mul]
            exact (mul_eq_zero.mp this).resolve_left hcz
          have hd : lz * cz⁻¹ ≠ 0 := by
            intro h0
            have hlz0 : lz = 0 := by
              have := congrArg (· * cz) h0
              simp [inv_mul_cancel_right₀ hcz] at this
              exact this
            exact vec_ne_zero l (Prod.ext hlx0 (Prod.ext hly0 hlz0))
          refine ⟨lz * cz⁻¹, hd, Prod.ext ?_ (Prod.ext ?_ ?_)⟩
          · simp [hlx0, hcx]
          · simp [hly0, hcy]
          · rw [inv_mul_cancel_right₀ hcz]
    obtain ⟨d, hd, hdl⟩ := hprop
    apply eq_of_scale (c := d * c0⁻¹) (mul_ne_zero hd (inv_ne_zero hc0))
    have hv0 : vec l0 = (c0 * cx, c0 * cy, c0 * cz) := hvec0
    rw [hv0]
    have hmul : ∀ t : ZMod q0, d * c0⁻¹ * (c0 * t) = d * t := fun t => by
      calc d * c0⁻¹ * (c0 * t) = d * (c0⁻¹ * c0) * t := by ring
        _ = d * t := by rw [inv_mul_cancel₀ hc0]; ring
    simp only [hmul]
    exact hdl

lemma card_line_Pt (l : Pt) : Fintype.card { u : Pt // incPt u l } = q0 + 1 := by
  have hcard : Fintype.card (ZMod q0 ⊕ Unit) = q0 + 1 := by simp
  rw [← hcard]
  symm
  apply Fintype.card_congr
  rcases l with ⟨a, b⟩ | b | ⟨⟩
  · by_cases ha : a = 0
    · subst ha
      by_cases hb : b = 0
      · subst hb
        refine
          { toFun := fun s => match s with
              | Sum.inl z => ⟨Sum.inr (Sum.inl z), by simp [incPt, dot, vec]⟩
              | Sum.inr () => ⟨Sum.inr (Sum.inr ()), by simp [incPt, dot, vec]⟩
            invFun := fun ⟨u, hu⟩ => match u, hu with
              | Sum.inl (x, y), hu => by simp [incPt, dot, vec] at hu
              | Sum.inr (Sum.inl z), _ => Sum.inl z
              | Sum.inr (Sum.inr ()), _ => Sum.inr ()
            left_inv := fun s => by rcases s with z | ⟨⟩ <;> rfl
            right_inv := fun ⟨u, hu⟩ => by
              rcases u with ⟨x, y⟩ | z | ⟨⟩
              · simp [incPt, dot, vec] at hu
              · rfl
              · rfl }
      · refine
          { toFun := fun s => match s with
              | Sum.inl y => ⟨Sum.inl (y, -b⁻¹), by
                  simp only [incPt, dot, vec]
                  rw [mul_one, mul_zero, add_zero, neg_mul, inv_mul_cancel₀ hb]
                  ring⟩
              | Sum.inr () => ⟨Sum.inr (Sum.inl 0), by simp [incPt, dot, vec]⟩
            invFun := fun ⟨u, hu⟩ => match u, hu with
              | Sum.inl (y, _), _ => Sum.inl y
              | Sum.inr (Sum.inl _), _ => Sum.inr ()
              | Sum.inr (Sum.inr ()), hu => by simp [incPt, dot, vec, hb] at hu
            left_inv := fun s => by rcases s with y | ⟨⟩ <;> rfl
            right_inv := fun ⟨u, hu⟩ => by
              rcases u with ⟨y, z⟩ | z | ⟨⟩
              · ext; simp only [incPt, dot, vec] at hu
                have hz : z = -b⁻¹ := by
                  have h1 : 1 + z * b = 0 := by linear_combination hu
                  have h2 : z * b = -1 := by linear_combination h1
                  have h3 := congrArg (· * b⁻¹) h2
                  simp [mul_assoc, mul_inv_cancel₀ hb] at h3
                  exact h3
                simp [hz]
              · ext; simp only [incPt, dot, vec] at hu
                have hz : z = 0 := by
                  have : z * b = 0 := by linear_combination hu
                  exact (mul_eq_zero.mp this).resolve_right hb
                simp [hz]
              · simp [incPt, dot, vec, hb] at hu }
    · by_cases hb : b = 0
      · subst hb
        refine
          { toFun := fun s => match s with
              | Sum.inl z => ⟨Sum.inl (-a⁻¹, z), by
                  simp [incPt, dot, vec, neg_mul, inv_mul_cancel₀ ha]⟩
              | Sum.inr () => ⟨Sum.inr (Sum.inr ()), by simp [incPt, dot, vec]⟩
            invFun := fun ⟨u, hu⟩ => match u, hu with
              | Sum.inl (_, z), _ => Sum.inl z
              | Sum.inr (Sum.inl _), hu => by simp [incPt, dot, vec, ha] at hu
              | Sum.inr (Sum.inr ()), _ => Sum.inr ()
            left_inv := fun s => by rcases s with z | ⟨⟩ <;> rfl
            right_inv := fun ⟨u, hu⟩ => by
              rcases u with ⟨y, z⟩ | z | ⟨⟩
              · ext; simp only [incPt, dot, vec] at hu
                have hy : y = -a⁻¹ := by
                  have h2 : y * a = -1 := by linear_combination hu
                  have h3 := congrArg (· * a⁻¹) h2
                  simp [mul_assoc, mul_inv_cancel₀ ha] at h3
                  exact h3
                simp [hy]
              · simp [incPt, dot, vec, ha] at hu
              · rfl }
      · refine
          { toFun := fun s => match s with
              | Sum.inl z => ⟨Sum.inl (-a⁻¹ * (1 + z * b), z), by
                  simp only [incPt, dot, vec]
                  calc 1 * 1 + -a⁻¹ * (1 + z * b) * a + z * b
                      = 1 - (a⁻¹ * a) * (1 + z * b) + z * b := by ring
                    _ = 0 := by rw [inv_mul_cancel₀ ha]; ring⟩
              | Sum.inr () => ⟨Sum.inr (Sum.inl (-b⁻¹ * a)), by
                  simp only [incPt, dot, vec]
                  calc 0 * 1 + 1 * a + -b⁻¹ * a * b
                      = a - (b⁻¹ * b) * a := by ring
                    _ = 0 := by rw [inv_mul_cancel₀ hb]; ring⟩
            invFun := fun ⟨u, hu⟩ => match u, hu with
              | Sum.inl (_, z), _ => Sum.inl z
              | Sum.inr (Sum.inl _), _ => Sum.inr ()
              | Sum.inr (Sum.inr ()), hu => by simp [incPt, dot, vec, hb] at hu
            left_inv := fun s => by rcases s with z | ⟨⟩ <;> rfl
            right_inv := fun ⟨u, hu⟩ => by
              rcases u with ⟨y, z⟩ | z | ⟨⟩
              · ext; simp only [incPt, dot, vec] at hu
                have hy : y = -a⁻¹ * (1 + z * b) := by
                  have h2 : y * a = -(1 + z * b) := by linear_combination hu
                  have h3 := congrArg (· * a⁻¹) h2
                  simp [mul_assoc, mul_inv_cancel₀ ha] at h3
                  linear_combination h3
                simp [hy]
              · ext; simp only [incPt, dot, vec] at hu
                have hz : z = -b⁻¹ * a := by
                  have h2 : z * b = -a := by linear_combination hu
                  have h3 := congrArg (· * b⁻¹) h2
                  simp [mul_assoc, mul_inv_cancel₀ hb] at h3
                  linear_combination h3
                simp [hz]
              · simp [incPt, dot, vec, hb] at hu }
  · by_cases hb : b = 0
    · subst hb
      refine
        { toFun := fun s => match s with
            | Sum.inl z => ⟨Sum.inl (0, z), by simp [incPt, dot, vec]⟩
            | Sum.inr () => ⟨Sum.inr (Sum.inr ()), by simp [incPt, dot, vec]⟩
          invFun := fun ⟨u, hu⟩ => match u, hu with
            | Sum.inl (_, z), _ => Sum.inl z
            | Sum.inr (Sum.inl _), hu => by simp [incPt, dot, vec] at hu
            | Sum.inr (Sum.inr ()), _ => Sum.inr ()
          left_inv := fun s => by rcases s with z | ⟨⟩ <;> rfl
          right_inv := fun ⟨u, hu⟩ => by
            rcases u with ⟨y, z⟩ | z | ⟨⟩
            · ext; simp only [incPt, dot, vec] at hu
              have hy : y = 0 := by linear_combination hu
              simp [hy]
            · simp [incPt, dot, vec] at hu
            · rfl }
    · refine
        { toFun := fun s => match s with
            | Sum.inl z => ⟨Sum.inl (-z * b, z), by simp [incPt, dot, vec]⟩
            | Sum.inr () => ⟨Sum.inr (Sum.inl (-b⁻¹)), by
                simp [incPt, dot, vec, neg_mul, inv_mul_cancel₀ hb]⟩
          invFun := fun ⟨u, hu⟩ => match u, hu with
            | Sum.inl (_, z), _ => Sum.inl z
            | Sum.inr (Sum.inl _), _ => Sum.inr ()
            | Sum.inr (Sum.inr ()), hu => by simp [incPt, dot, vec, hb] at hu
          left_inv := fun s => by rcases s with z | ⟨⟩ <;> rfl
          right_inv := fun ⟨u, hu⟩ => by
            rcases u with ⟨y, z⟩ | z | ⟨⟩
            · ext; simp only [incPt, dot, vec] at hu
              have hy : y = -z * b := by linear_combination hu
              simp [hy]
            · ext; simp only [incPt, dot, vec] at hu
              have hz : z = -b⁻¹ := by
                have h2 : z * b = -1 := by linear_combination hu
                have h3 := congrArg (· * b⁻¹) h2
                simp [mul_assoc, mul_inv_cancel₀ hb] at h3
                exact h3
              simp [hz]
            · simp [incPt, dot, vec, hb] at hu }
  · refine
      { toFun := fun s => match s with
          | Sum.inl a => ⟨Sum.inl (a, 0), by simp [incPt, dot, vec]⟩
          | Sum.inr () => ⟨Sum.inr (Sum.inl 0), by simp [incPt, dot, vec]⟩
        invFun := fun ⟨u, hu⟩ => match u, hu with
          | Sum.inl (a, _), _ => Sum.inl a
          | Sum.inr (Sum.inl _), _ => Sum.inr ()
          | Sum.inr (Sum.inr ()), hu => by simp [incPt, dot, vec] at hu
        left_inv := fun s => by rcases s with a | ⟨⟩ <;> rfl
        right_inv := fun ⟨u, hu⟩ => by
          rcases u with ⟨a, b⟩ | b | ⟨⟩
          · ext; simp only [incPt, dot, vec] at hu
            have hb : b = 0 := by linear_combination hu
            simp [hb]
          · ext; simp only [incPt, dot, vec] at hu
            have hb : b = 0 := by linear_combination hu
            simp [hb]
          · simp [incPt, dot, vec] at hu }

lemma card_Pt : Fintype.card Pt = N0 := by
  simp [Pt, N0]
  ring

/-! ## Part 2: No IsAO2 circuit of size ≤ 2 * N computes PG(2, q) incidence -/

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

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

lemma wiresFrom_getD_gate (gs : List Gate) : ∀ (w : List Bool) (j : ℕ) (hj : j < gs.length),
    (∀ u ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, u < w.length + j) →
    (wiresFrom gs w).getD (w.length + j) false =
      (gs.getD j ⟨GateOp.or, []⟩).op.eval
        ((gs.getD j ⟨GateOp.or, []⟩).inputs.map fun u => (wiresFrom gs w).getD u false) := by
  induction gs with
  | nil => intro w j hj; simp at hj
  | cons g gs ih =>
    intro w j hj hrb
    set b := g.op.eval (g.inputs.map fun i => w.getD i false)
    cases j with
    | zero =>
      have h0 : (g :: gs).getD 0 ⟨GateOp.or, []⟩ = g := rfl
      rw [h0] at hrb ⊢
      have hstep : wiresFrom (g :: gs) w = wiresFrom gs (w ++ [b]) := rfl
      rw [hstep, Nat.add_zero]
      have hlt : w.length < (w ++ [b]).length := by simp
      rw [wiresFrom_getD_lt gs (w ++ [b]) hlt]
      have hwb : (w ++ [b]).getD w.length false = b := by
        simp [List.getD_eq_getElem?_getD]
      rw [hwb]
      dsimp only [b]
      congr 1
      apply List.map_congr_left
      intro u hu
      have hu' : u < w.length := by simpa using hrb u hu
      have hu'' : u < (w ++ [b]).length := by simp; omega
      rw [wiresFrom_getD_lt gs (w ++ [b]) hu'']
      simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hu']
    | succ j' =>
      have hstep : wiresFrom (g :: gs) w = wiresFrom gs (w ++ [b]) := rfl
      have hget : (g :: gs).getD (j' + 1) ⟨GateOp.or, []⟩ = gs.getD j' ⟨GateOp.or, []⟩ := rfl
      rw [hget] at hrb ⊢
      rw [hstep]
      have hj' : j' < gs.length := by simpa using hj
      have hlen : (w ++ [b]).length + j' = w.length + (j' + 1) := by simp; omega
      rw [← hlen]
      apply ih (w ++ [b]) j' hj'
      intro u hu
      rw [hlen]
      exact hrb u hu

def wval {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma wval_lt {n : ℕ} (C : Circuit) (x : Fin n → Bool) {i : ℕ} (hi : i < n) :
    wval C x i = x ⟨i, hi⟩ := by
  unfold wval Circuit.wires
  have h : i < (List.ofFn x).length := by simp [hi]
  rw [show C.gates.foldl _ (List.ofFn x) = wiresFrom C.gates (List.ofFn x) from rfl]
  rw [wiresFrom_getD_lt C.gates (List.ofFn x) h]
  simp [List.getD_eq_getElem?_getD, hi]

lemma wval_ge {n : ℕ} (C : Circuit) (x : Fin n → Bool) {w : ℕ} (hw : n + C.gates.length ≤ w) :
    wval C x w = false := by
  unfold wval Circuit.wires
  rw [show C.gates.foldl _ (List.ofFn x) = wiresFrom C.gates (List.ofFn x) from rfl]
  have hlen : (wiresFrom C.gates (List.ofFn x)).length = n + C.gates.length := by
    rw [wiresFrom_length, List.length_ofFn]
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : (wiresFrom C.gates (List.ofFn x)).length ≤ w)]

lemma wval_gate {n : ℕ} (C : Circuit) (hAO : IsAO2 n C) (x : Fin n → Bool)
    {j : ℕ} (hj : j < C.gates.length) :
    wval C x (n + j) =
      if (gateAt C j).op = GateOp.and then
        wval C x ((gateAt C j).inputs.getD 0 0) && wval C x ((gateAt C j).inputs.getD 1 0)
      else
        wval C x ((gateAt C j).inputs.getD 0 0) || wval C x ((gateAt C j).inputs.getD 1 0) := by
  have hrb := hAO.2.1
  have hlen2 : (gateAt C j).inputs.length = 2 := by
    apply hAO.2.2
    unfold gateAt
    rw [List.getD_eq_getElem _ _ hj]
    exact List.getElem_mem hj
  have hop : (gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or := by
    apply hAO.1
    unfold gateAt
    rw [List.getD_eq_getElem _ _ hj]
    exact List.getElem_mem hj
  have hmain : wval C x (n + j) =
      (gateAt C j).op.eval ((gateAt C j).inputs.map (wval C x)) := by
    unfold wval Circuit.wires
    rw [show C.gates.foldl _ (List.ofFn x) = wiresFrom C.gates (List.ofFn x) from rfl]
    have h1 := wiresFrom_getD_gate C.gates (List.ofFn x) j hj (by
      intro u hu; rw [List.length_ofFn]; exact hrb j hj u hu)
    simpa [List.length_ofFn, gateAt] using h1
  rw [hmain]
  rcases hlist : (gateAt C j).inputs with _ | ⟨a, _ | ⟨b, _ | _⟩⟩ <;> simp [hlist] at hlen2
  rcases hop with hop | hop <;> simp [hop, GateOp.eval, hlist]

lemma wval_mono {n : ℕ} (C : Circuit) (hAO : IsAO2 n C) {x y : Fin n → Bool}
    (hxy : ∀ i, x i = true → y i = true) :
    ∀ w, wval C x w = true → wval C y w = true := by
  intro w
  induction w using Nat.strongRecOn with
  | ind w ih =>
    intro hx
    by_cases hlt : w < n
    · rw [wval_lt C x hlt] at hx
      rw [wval_lt C y hlt]
      exact hxy ⟨w, hlt⟩ hx
    · by_cases hge : n + C.gates.length ≤ w
      · rw [wval_ge C x hge] at hx; cases hx
      · have hj : w - n < C.gates.length := by omega
        have hw : w = n + (w - n) := by omega
        have hlen2 : (gateAt C (w - n)).inputs.length = 2 := by
          apply hAO.2.2
          unfold gateAt
          rw [List.getD_eq_getElem _ _ hj]
          exact List.getElem_mem hj
        have h0mem : (gateAt C (w - n)).inputs.getD 0 0 ∈ (gateAt C (w - n)).inputs := by
          rcases hlist : (gateAt C (w - n)).inputs with _ | ⟨a, _ | ⟨b, _ | _⟩⟩ <;> simp [hlist] at hlen2 ⊢
        have h1mem : (gateAt C (w - n)).inputs.getD 1 0 ∈ (gateAt C (w - n)).inputs := by
          rcases hlist : (gateAt C (w - n)).inputs with _ | ⟨a, _ | ⟨b, _ | _⟩⟩ <;> simp [hlist] at hlen2 ⊢
        have ha : (gateAt C (w - n)).inputs.getD 0 0 < w := by
          have := hAO.2.1 (w - n) hj _ h0mem; omega
        have hb : (gateAt C (w - n)).inputs.getD 1 0 < w := by
          have := hAO.2.1 (w - n) hj _ h1mem; omega
        rw [hw] at hx ⊢
        rw [wval_gate C hAO x hj] at hx
        rw [wval_gate C hAO y hj]
        split_ifs at hx ⊢
        · simp only [Bool.and_eq_true] at hx ⊢
          exact ⟨ih _ ha hx.1, ih _ hb hx.2⟩
        · simp only [Bool.or_eq_true] at hx ⊢
          exact hx.elim (fun h => Or.inl (ih _ ha h)) (fun h => Or.inr (ih _ hb h))

def cone (n : ℕ) (C : Circuit) (w : ℕ) : Finset ℕ :=
  if n ≤ w ∧ w - n < C.gates.length then
    insert w (((gateAt C (w - n)).inputs.toFinset.filter (· < w)).attach.biUnion
      (fun u => cone n C u.1))
  else {w}
termination_by w
decreasing_by exact (Finset.mem_filter.mp u.2).2

lemma mem_cone_self (n : ℕ) (C : Circuit) (w : ℕ) : w ∈ cone n C w := by
  rw [cone]
  split_ifs <;> simp

lemma mem_cone_iff_of_gate {n : ℕ} (C : Circuit) (hrb : ReadsBack n C) {w : ℕ}
    (hw1 : n ≤ w) (hw2 : w - n < C.gates.length) (z : ℕ) :
    z ∈ cone n C w ↔ z = w ∨ ∃ u ∈ (gateAt C (w - n)).inputs, z ∈ cone n C u := by
  rw [cone]
  simp only [hw1, hw2, and_self, ↓reduceIte, Finset.mem_insert, Finset.mem_biUnion,
    Finset.mem_attach, true_and, Subtype.exists, Finset.mem_filter, List.mem_toFinset]
  constructor
  · rintro (rfl | ⟨u, ⟨hu, _⟩, hz⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨u, hu, hz⟩
  · rintro (rfl | ⟨u, hu, hz⟩)
    · exact Or.inl rfl
    · have hult : u < w := by have := hrb (w - n) hw2 u hu; omega
      exact Or.inr ⟨u, ⟨hu, hult⟩, hz⟩

lemma mem_cone_iff_of_not_gate {n : ℕ} (C : Circuit) {w : ℕ}
    (hw : ¬ (n ≤ w ∧ w - n < C.gates.length)) (z : ℕ) :
    z ∈ cone n C w ↔ z = w := by
  rw [cone]
  simp [hw]

lemma mem_cone_le (n : ℕ) (C : Circuit) (hrb : ReadsBack n C) :
    ∀ w z, z ∈ cone n C w → z ≤ w := by
  intro w
  induction w using Nat.strongRecOn with
  | ind w ih =>
    intro z hz
    by_cases hw : n ≤ w ∧ w - n < C.gates.length
    · rw [mem_cone_iff_of_gate C hrb hw.1 hw.2] at hz
      rcases hz with rfl | ⟨u, hu, hzu⟩
      · exact le_rfl
      · have hult : u < w := by have := hrb (w - n) hw.2 u hu; omega
        exact le_trans (ih u hult z hzu) (le_of_lt hult)
    · rw [mem_cone_iff_of_not_gate C hw] at hz
      subst hz; exact le_rfl

lemma cone_subset_of_mem (n : ℕ) (C : Circuit) (hrb : ReadsBack n C) :
    ∀ w u, u ∈ cone n C w → cone n C u ⊆ cone n C w := by
  intro w
  induction w using Nat.strongRecOn with
  | ind w ih =>
    intro u hu
    by_cases hw : n ≤ w ∧ w - n < C.gates.length
    · rw [mem_cone_iff_of_gate C hrb hw.1 hw.2] at hu
      rcases hu with rfl | ⟨v, hv, huv⟩
      · exact Finset.Subset.refl _
      · have hvlt : v < w := by have := hrb (w - n) hw.2 v hv; omega
        intro z hz
        have hzv : z ∈ cone n C v := ih v hvlt u huv hz
        rw [mem_cone_iff_of_gate C hrb hw.1 hw.2]
        exact Or.inr ⟨v, hv, hzv⟩
    · rw [mem_cone_iff_of_not_gate C hw] at hu
      subst hu; exact Finset.Subset.refl _

lemma mem_cone_of_input (n : ℕ) (C : Circuit) (hrb : ReadsBack n C) {w u : ℕ}
    (hw1 : n ≤ w) (hw2 : w - n < C.gates.length) (hu : u ∈ (gateAt C (w - n)).inputs) :
    u ∈ cone n C w := by
  rw [mem_cone_iff_of_gate C hrb hw1 hw2]
  exact Or.inr ⟨u, hu, mem_cone_self n C u⟩

lemma exists_reader_of_mem_cone (n : ℕ) (C : Circuit) (hrb : ReadsBack n C) :
    ∀ w z, z ∈ cone n C w → z < w →
    ∃ g ∈ cone n C w, n ≤ g ∧ g - n < C.gates.length ∧ z ∈ (gateAt C (g - n)).inputs := by
  intro w
  induction w using Nat.strongRecOn with
  | ind w ih =>
    intro z hz hzw
    by_cases hw : n ≤ w ∧ w - n < C.gates.length
    · rw [mem_cone_iff_of_gate C hrb hw.1 hw.2] at hz
      rcases hz with rfl | ⟨u, hu, hzu⟩
      · omega
      · by_cases hzu_eq : z = u
        · subst hzu_eq
          exact ⟨w, mem_cone_self n C w, hw.1, hw.2, hu⟩
        · have hule : z ≤ u := mem_cone_le n C hrb u z hzu
          have hzlt : z < u := lt_of_le_of_ne hule hzu_eq
          have hult : u < w := by have := hrb (w - n) hw.2 u hu; omega
          obtain ⟨g, hgu, hg1, hg2, hgz⟩ := ih u hult z hzu hzlt
          refine ⟨g, ?_, hg1, hg2, hgz⟩
          exact cone_subset_of_mem n C hrb w u (mem_cone_of_input n C hrb hw.1 hw.2 hu) hgu
    · rw [mem_cone_iff_of_not_gate C hw] at hz
      omega

lemma wval_eq_of_cone {n : ℕ} (C : Circuit) (hAO : IsAO2 n C) {x y : Fin n → Bool} :
    ∀ w, (∀ i : Fin n, i.val ∈ cone n C w → x i = y i) → wval C x w = wval C y w := by
  intro w
  induction w using Nat.strongRecOn with
  | ind w ih =>
    intro hxy
    by_cases hlt : w < n
    · rw [wval_lt C x hlt, wval_lt C y hlt]
      exact hxy ⟨w, hlt⟩ (mem_cone_self n C w)
    · by_cases hge : n + C.gates.length ≤ w
      · rw [wval_ge C x hge, wval_ge C y hge]
      · have hw1 : n ≤ w := by omega
        have hw2 : w - n < C.gates.length := by omega
        have hw : w = n + (w - n) := by omega
        have hlen2 : (gateAt C (w - n)).inputs.length = 2 := by
          apply hAO.2.2; unfold gateAt; rw [List.getD_eq_getElem _ _ hw2]; exact List.getElem_mem hw2
        have h0mem : (gateAt C (w - n)).inputs.getD 0 0 ∈ (gateAt C (w - n)).inputs := by
          rcases hlist : (gateAt C (w - n)).inputs with _ | ⟨a, _ | ⟨b, _ | _⟩⟩ <;> simp [hlist] at hlen2 ⊢
        have h1mem : (gateAt C (w - n)).inputs.getD 1 0 ∈ (gateAt C (w - n)).inputs := by
          rcases hlist : (gateAt C (w - n)).inputs with _ | ⟨a, _ | ⟨b, _ | _⟩⟩ <;> simp [hlist] at hlen2 ⊢
        have ha : (gateAt C (w - n)).inputs.getD 0 0 < w := by
          have := hAO.2.1 (w - n) hw2 _ h0mem; omega
        have hb : (gateAt C (w - n)).inputs.getD 1 0 < w := by
          have := hAO.2.1 (w - n) hw2 _ h1mem; omega
        have hca := cone_subset_of_mem n C hAO.2.1 w _ (mem_cone_of_input n C hAO.2.1 hw1 hw2 h0mem)
        have hcb := cone_subset_of_mem n C hAO.2.1 w _ (mem_cone_of_input n C hAO.2.1 hw1 hw2 h1mem)
        have hva := ih _ ha (fun i hi => hxy i (hca hi))
        have hvb := ih _ hb (fun i hi => hxy i (hcb hi))
        rw [hw, wval_gate C hAO x hw2, wval_gate C hAO y hw2, hva, hvb]

def evalMod {n : ℕ} (C : Circuit) (wStar : ℕ) (c : Bool) (x : Fin n → Bool) (w : ℕ) : Bool :=
  if w = wStar then c
  else if n ≤ w ∧ w - n < C.gates.length then
    let g := gateAt C (w - n)
    let a := g.inputs.getD 0 0
    let b := g.inputs.getD 1 0
    let va := if a < w then evalMod C wStar c x a else false
    let vb := if b < w then evalMod C wStar c x b else false
    if g.op = GateOp.and then va && vb else va || vb
  else if h : w < n then x ⟨w, h⟩ else false
termination_by w

lemma evalMod_eq_wval {n : ℕ} (C : Circuit) (hAO : IsAO2 n C) (wStar : ℕ) (x : Fin n → Bool) :
    ∀ w, evalMod C wStar (wval C x wStar) x w = wval C x w := by
  intro w
  induction w using Nat.strongRecOn with
  | ind w ih =>
    rw [evalMod]
    split_ifs with hws hw
    · subst hws; rfl
    · have hlen2 : (gateAt C (w - n)).inputs.length = 2 := by
        apply hAO.2.2; unfold gateAt; rw [List.getD_eq_getElem _ _ hw.2]; exact List.getElem_mem hw.2
      have h0mem : (gateAt C (w - n)).inputs.getD 0 0 ∈ (gateAt C (w - n)).inputs := by
        rcases hlist : (gateAt C (w - n)).inputs with _ | ⟨a, _ | ⟨b, _ | _⟩⟩ <;> simp [hlist] at hlen2 ⊢
      have h1mem : (gateAt C (w - n)).inputs.getD 1 0 ∈ (gateAt C (w - n)).inputs := by
        rcases hlist : (gateAt C (w - n)).inputs with _ | ⟨a, _ | ⟨b, _ | _⟩⟩ <;> simp [hlist] at hlen2 ⊢
      have ha : (gateAt C (w - n)).inputs.getD 0 0 < w := by
        have := hAO.2.1 (w - n) hw.2 _ h0mem; omega
      have hb : (gateAt C (w - n)).inputs.getD 1 0 < w := by
        have := hAO.2.1 (w - n) hw.2 _ h1mem; omega
      have hweq : w = n + (w - n) := by omega
      dsimp only
      simp only [ha, hb, ↓reduceIte]
      rw [ih _ ha, ih _ hb]
      conv_rhs => rw [hweq, wval_gate C hAO x hw.2]
    · rename_i hlt
      exact (wval_lt C x hlt).symm
    · rename_i hlt
      have hge : n + C.gates.length ≤ w := by omega
      exact (wval_ge C x hge).symm

lemma evalMod_mono {n : ℕ} (C : Circuit) (wStar : ℕ) {c1 c2 : Bool} (hc : c1 = true → c2 = true)
    {x y : Fin n → Bool} (hxy : ∀ i, x i = true → y i = true) :
    ∀ w, evalMod C wStar c1 x w = true → evalMod C wStar c2 y w = true := by
  intro w
  induction w using Nat.strongRecOn with
  | ind w ih =>
    intro hx
    rw [evalMod] at hx ⊢
    by_cases hws : w = wStar
    · rw [if_pos hws] at hx ⊢; exact hc hx
    · rw [if_neg hws] at hx ⊢
      by_cases hw : n ≤ w ∧ w - n < C.gates.length
      · rw [if_pos hw] at hx ⊢
        dsimp only at hx ⊢
        have hma : (if (gateAt C (w - n)).inputs.getD 0 0 < w then evalMod C wStar c1 x ((gateAt C (w - n)).inputs.getD 0 0) else false) = true →
            (if (gateAt C (w - n)).inputs.getD 0 0 < w then evalMod C wStar c2 y ((gateAt C (w - n)).inputs.getD 0 0) else false) = true := by
          split_ifs with ha
          · exact ih _ ha
          · intro h; cases h
        have hmb : (if (gateAt C (w - n)).inputs.getD 1 0 < w then evalMod C wStar c1 x ((gateAt C (w - n)).inputs.getD 1 0) else false) = true →
            (if (gateAt C (w - n)).inputs.getD 1 0 < w then evalMod C wStar c2 y ((gateAt C (w - n)).inputs.getD 1 0) else false) = true := by
          split_ifs with hb
          · exact ih _ hb
          · intro h; cases h
        by_cases hop : (gateAt C (w - n)).op = GateOp.and
        · rw [if_pos hop] at hx ⊢
          simp only [Bool.and_eq_true] at hx ⊢
          exact ⟨hma hx.1, hmb hx.2⟩
        · rw [if_neg hop] at hx ⊢
          simp only [Bool.or_eq_true] at hx ⊢
          exact hx.elim (fun h => Or.inl (hma h)) (fun h => Or.inr (hmb h))
      · rw [if_neg hw] at hx ⊢
        by_cases hlt : w < n
        · rw [dif_pos hlt] at hx ⊢; exact hxy ⟨w, hlt⟩ hx
        · rw [dif_neg hlt] at hx; cases hx

/-! ## Abstract No-P4 lemma for read-once monotone circuits -/

def ind1 {n : ℕ} (u : Fin n) : Fin n → Bool := fun i => decide (i = u)
def ind2 {n : ℕ} (u v : Fin n) : Fin n → Bool := fun i => decide (i = u ∨ i = v)
def zeroIn {n : ℕ} : Fin n → Bool := fun _ => false

lemma bool_eq_of_ne {a b c : Bool} (ha : a ≠ c) (hb : b ≠ c) : a = b := by
  cases a <;> cases b <;> cases c <;> simp_all

lemma no_P4 {n : ℕ} (A : Finset ℕ) (H : ℕ → (Fin n → Bool) → Bool) (S : ℕ → Finset ℕ)
    (hMono : ∀ w ∈ A, ∀ x y : Fin n → Bool, (∀ i, x i = true → y i = true) → H w x = true → H w y = true)
    (hDep : ∀ w ∈ A, ∀ x y : Fin n → Bool, (∀ i : Fin n, i.val ∈ S w → x i = y i) → H w x = H w y)
    (hStruct : ∀ w ∈ A,
      S w = ∅ ∨
      (∃ u < n, S w = {u}) ∨
      ∃ a ∈ A, ∃ b ∈ A, a < w ∧ b < w ∧ Disjoint (S a) (S b) ∧ S w ⊆ S a ∪ S b ∧
        ((∀ x, H w x = (H a x && H b x)) ∨ (∀ x, H w x = (H a x || H b x))))
    {v1 v2 v3 v4 : Fin n}
    (h12 : v1 ≠ v2) (h13 : v1 ≠ v3) (h14 : v1 ≠ v4)
    (h23 : v2 ≠ v3) (h24 : v2 ≠ v4) (h34 : v3 ≠ v4) :
    ∀ w ∈ A, ¬ (
      H w (ind1 v1) = false ∧ H w (ind1 v2) = false ∧ H w (ind1 v3) = false ∧ H w (ind1 v4) = false ∧
      H w (ind2 v1 v2) = true ∧ H w (ind2 v2 v3) = true ∧ H w (ind2 v3 v4) = true ∧
      H w (ind2 v1 v4) = false) := by
  intro w
  induction w using Nat.strongRecOn with
  | ind w ih =>
    intro hwA hP4
    rcases hP4 with ⟨hf1, hf2, hf3, hf4, ht12, ht23, ht34, hf14⟩
    have hmem : ∀ u v : Fin n, H w (ind1 v) = false → H w (ind2 u v) = true → u.val ∈ S w := by
      intro u v hfv htuv
      by_contra hu
      have heq : H w (ind2 u v) = H w (ind1 v) := by
        apply hDep w hwA
        intro i hi
        have hiu : i ≠ u := fun h => hu (h ▸ hi)
        simp [ind2, ind1, hiu]
      rw [htuv, hfv] at heq; cases heq
    have hv1 : v1.val ∈ S w := hmem v1 v2 hf2 ht12
    have hv2 : v2.val ∈ S w := hmem v2 v1 hf1 (by
      have : ind2 v2 v1 = ind2 v1 v2 := by funext i; simp [ind2, or_comm]
      rw [this]; exact ht12)
    have hv3 : v3.val ∈ S w := hmem v3 v4 hf4 ht34
    have hv4 : v4.val ∈ S w := hmem v4 v3 hf3 (by
      have : ind2 v4 v3 = ind2 v3 v4 := by funext i; simp [ind2, or_comm]
      rw [this]; exact ht34)
    rcases hStruct w hwA with hEmpty | ⟨u, _, hSing⟩ | ⟨a, haA, b, hbA, haw, hbw, hDisj, hSub, hOp⟩
    · rw [hEmpty] at hv1; simp at hv1
    · rw [hSing, Finset.mem_singleton] at hv1 hv2
      exact h12 (Fin.ext (hv1.trans hv2.symm))
    · have hmemAB : ∀ v : Fin n, v.val ∈ S w → v.val ∈ S a ∨ v.val ∈ S b := fun v hv =>
        Finset.mem_union.mp (hSub hv)
      have hNotEmptySide : ∀ (a' b' : ℕ), a' ∈ A → b' ∈ A → b' < w →
          ((∀ x, H w x = (H a' x && H b' x)) ∨ (∀ x, H w x = (H a' x || H b' x))) →
          (v1.val ∉ S a' ∧ v2.val ∉ S a' ∧ v3.val ∉ S a' ∧ v4.val ∉ S a') → False := by
        intro a' b' ha'A hb'A hb'w hOp' hOut
        have hConst : ∀ x : Fin n → Bool,
            (∀ i, x i = true → i = v1 ∨ i = v2 ∨ i = v3 ∨ i = v4) →
            H a' x = H a' zeroIn := by
          intro x hx
          apply hDep a' ha'A
          intro i hi
          cases hxi : x i
          · rfl
          · exfalso
            rcases hx i hxi with rfl | rfl | rfl | rfl
            · exact hOut.1 hi
            · exact hOut.2.1 hi
            · exact hOut.2.2.1 hi
            · exact hOut.2.2.2 hi
        have hsupp1 : ∀ u, u = v1 ∨ u = v2 ∨ u = v3 ∨ u = v4 →
            ∀ i, ind1 u i = true → i = v1 ∨ i = v2 ∨ i = v3 ∨ i = v4 := by
          intro u hu i hi; simp [ind1] at hi; subst hi; exact hu
        have hsupp2 : ∀ u v, (u = v1 ∨ u = v2 ∨ u = v3 ∨ u = v4) →
            (v = v1 ∨ v = v2 ∨ v = v3 ∨ v = v4) →
            ∀ i, ind2 u v i = true → i = v1 ∨ i = v2 ∨ i = v3 ∨ i = v4 := by
          intro u v hu hv i hi; simp [ind2] at hi; rcases hi with rfl | rfl <;> assumption
        rcases hOp' with hAnd | hOr
        · cases hc : H a' zeroIn
          · have := hAnd (ind2 v1 v2)
            rw [hConst _ (hsupp2 v1 v2 (Or.inl rfl) (Or.inr (Or.inl rfl))), hc] at this
            simp [ht12] at this
          · apply ih b' hb'w hb'A
            refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
            · have := hAnd (ind1 v1); rw [hConst _ (hsupp1 v1 (Or.inl rfl)), hc] at this; simpa [hf1] using this.symm
            · have := hAnd (ind1 v2); rw [hConst _ (hsupp1 v2 (Or.inr (Or.inl rfl))), hc] at this; simpa [hf2] using this.symm
            · have := hAnd (ind1 v3); rw [hConst _ (hsupp1 v3 (Or.inr (Or.inr (Or.inl rfl)))), hc] at this; simpa [hf3] using this.symm
            · have := hAnd (ind1 v4); rw [hConst _ (hsupp1 v4 (Or.inr (Or.inr (Or.inr rfl)))), hc] at this; simpa [hf4] using this.symm
            · have := hAnd (ind2 v1 v2); rw [hConst _ (hsupp2 v1 v2 (Or.inl rfl) (Or.inr (Or.inl rfl))), hc] at this; simpa [ht12] using this.symm
            · have := hAnd (ind2 v2 v3); rw [hConst _ (hsupp2 v2 v3 (Or.inr (Or.inl rfl)) (Or.inr (Or.inr (Or.inl rfl)))), hc] at this; simpa [ht23] using this.symm
            · have := hAnd (ind2 v3 v4); rw [hConst _ (hsupp2 v3 v4 (Or.inr (Or.inr (Or.inl rfl))) (Or.inr (Or.inr (Or.inr rfl)))), hc] at this; simpa [ht34] using this.symm
            · have := hAnd (ind2 v1 v4); rw [hConst _ (hsupp2 v1 v4 (Or.inl rfl) (Or.inr (Or.inr (Or.inr rfl)))), hc] at this; simpa [hf14] using this.symm
        · cases hc : H a' zeroIn
          · apply ih b' hb'w hb'A
            refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
            · have := hOr (ind1 v1); rw [hConst _ (hsupp1 v1 (Or.inl rfl)), hc] at this; simpa [hf1] using this.symm
            · have := hOr (ind1 v2); rw [hConst _ (hsupp1 v2 (Or.inr (Or.inl rfl))), hc] at this; simpa [hf2] using this.symm
            · have := hOr (ind1 v3); rw [hConst _ (hsupp1 v3 (Or.inr (Or.inr (Or.inl rfl)))), hc] at this; simpa [hf3] using this.symm
            · have := hOr (ind1 v4); rw [hConst _ (hsupp1 v4 (Or.inr (Or.inr (Or.inr rfl)))), hc] at this; simpa [hf4] using this.symm
            · have := hOr (ind2 v1 v2); rw [hConst _ (hsupp2 v1 v2 (Or.inl rfl) (Or.inr (Or.inl rfl))), hc] at this; simpa [ht12] using this.symm
            · have := hOr (ind2 v2 v3); rw [hConst _ (hsupp2 v2 v3 (Or.inr (Or.inl rfl)) (Or.inr (Or.inr (Or.inl rfl)))), hc] at this; simpa [ht23] using this.symm
            · have := hOr (ind2 v3 v4); rw [hConst _ (hsupp2 v3 v4 (Or.inr (Or.inr (Or.inl rfl))) (Or.inr (Or.inr (Or.inr rfl)))), hc] at this; simpa [ht34] using this.symm
            · have := hOr (ind2 v1 v4); rw [hConst _ (hsupp2 v1 v4 (Or.inl rfl) (Or.inr (Or.inr (Or.inr rfl)))), hc] at this; simpa [hf14] using this.symm
          · have := hOr (ind1 v1)
            rw [hConst _ (hsupp1 v1 (Or.inl rfl)), hc] at this
            simp [hf1] at this
      have hOrCross : ∀ u v : Fin n,
          (∀ x, H w x = (H a x || H b x)) →
          H w (ind1 u) = false → H w (ind1 v) = false → H w (ind2 u v) = true →
          ((u.val ∈ S a ∧ v.val ∈ S b) ∨ (u.val ∈ S b ∧ v.val ∈ S a)) → False := by
        intro u v hOr hfu hfv htuv hcross
        have hstep : ∀ (a' b' : ℕ), a' ∈ A → b' ∈ A →
            (∀ x, H w x = (H a' x || H b' x)) →
            u.val ∈ S a' → v.val ∈ S b' → Disjoint (S a') (S b') → False := by
          intro a' b' ha'A hb'A hOr' hua' hvb' hD'
          have hva' : v.val ∉ S a' := Finset.disjoint_right.mp hD' hvb'
          have hub' : u.val ∉ S b' := Finset.disjoint_left.mp hD' hua'
          have h1 : H a' (ind2 u v) = H a' (ind1 u) := hDep a' ha'A _ _ (fun i hi => by
            have hiv : i ≠ v := fun h => hva' (h ▸ hi); simp [ind2, ind1, hiv])
          have h2 : H b' (ind2 u v) = H b' (ind1 v) := hDep b' hb'A _ _ (fun i hi => by
            have hiu : i ≠ u := fun h => hub' (h ▸ hi); simp [ind2, ind1, hiu])
          have ht := hOr' (ind2 u v)
          rw [htuv, h1, h2] at ht
          have hfu' := hOr' (ind1 u); rw [hfu] at hfu'
          have hfv' := hOr' (ind1 v); rw [hfv] at hfv'
          have hau : H a' (ind1 u) = false := by
            cases h : H a' (ind1 u)
            · rfl
            · rw [h] at hfu'; simp at hfu'
          have hbv : H b' (ind1 v) = false := by
            cases h : H b' (ind1 v)
            · rfl
            · rw [h] at hfv'; simp at hfv'
          rw [hau, hbv] at ht; simp at ht
        rcases hcross with ⟨hua, hvb⟩ | ⟨hub, hva⟩
        · exact hstep a b haA hbA hOr hua hvb hDisj
        · exact hstep b a hbA haA (fun x => by rw [hOr, Bool.or_comm]) hub hva hDisj.symm
      have hAndSame : ∀ (a' b' : ℕ), a' ∈ A → b' ∈ A → a' < w →
          (∀ x, H w x = (H a' x && H b' x)) → Disjoint (S a') (S b') →
          ∀ u v : Fin n, H w (ind2 u v) = true → u.val ∈ S a' → v.val ∈ S a' → False := by
        intro a' b' ha'A hb'A ha'w hAnd' hD' u v htuv hua' hva'
        have hub' : u.val ∉ S b' := Finset.disjoint_left.mp hD' hua'
        have hvb' : v.val ∉ S b' := Finset.disjoint_left.mp hD' hva'
        have hb0 : H b' zeroIn = true := by
          have h1 := hAnd' (ind2 u v); rw [htuv] at h1
          have h2 : H b' (ind2 u v) = H b' zeroIn := hDep b' hb'A _ _ (fun i hi => by
            have hiu : i ≠ u := fun h => hub' (h ▸ hi)
            have hiv : i ≠ v := fun h => hvb' (h ▸ hi)
            simp [ind2, zeroIn, hiu, hiv])
          rw [h2] at h1
          cases h : H b' zeroIn
          · rw [h] at h1; simp at h1
          · rfl
        have hball : ∀ x, H b' x = true := fun x => hMono b' hb'A zeroIn x (fun _ h => by cases h) hb0
        have heq : ∀ x, H w x = H a' x := fun x => by rw [hAnd' x, hball x, Bool.and_true]
        exact ih a' ha'w ha'A ⟨by rw [← heq]; exact hf1, by rw [← heq]; exact hf2,
          by rw [← heq]; exact hf3, by rw [← heq]; exact hf4, by rw [← heq]; exact ht12,
          by rw [← heq]; exact ht23, by rw [← heq]; exact ht34, by rw [← heq]; exact hf14⟩
      rcases hOp with hAnd | hOr
      · rcases hmemAB v1 hv1 with h1a | h1b <;>
        rcases hmemAB v2 hv2 with h2a | h2b <;>
        rcases hmemAB v3 hv3 with h3a | h3b <;>
        rcases hmemAB v4 hv4 with h4a | h4b
        all_goals
          try exact hAndSame a b haA hbA haw hAnd hDisj v1 v2 ht12 ‹_› ‹_›
          try exact hAndSame a b haA hbA haw hAnd hDisj v2 v3 ht23 ‹_› ‹_›
          try exact hAndSame a b haA hbA haw hAnd hDisj v3 v4 ht34 ‹_› ‹_›
          try exact hAndSame b a hbA haA hbw (fun x => by rw [hAnd, Bool.and_comm]) hDisj.symm v1 v2 ht12 ‹_› ‹_›
          try exact hAndSame b a hbA haA hbw (fun x => by rw [hAnd, Bool.and_comm]) hDisj.symm v2 v3 ht23 ‹_› ‹_›
          try exact hAndSame b a hbA haA hbw (fun x => by rw [hAnd, Bool.and_comm]) hDisj.symm v3 v4 ht34 ‹_› ‹_›
        · have h2na : v2.val ∉ S a := Finset.disjoint_right.mp hDisj h2b
          have h4na : v4.val ∉ S a := Finset.disjoint_right.mp hDisj h4b
          have h1nb : v1.val ∉ S b := Finset.disjoint_left.mp hDisj h1a
          have h3nb : v3.val ∉ S b := Finset.disjoint_left.mp hDisj h3a
          have ha1 : H a (ind1 v1) = true := by
            have := hAnd (ind2 v1 v2); rw [ht12] at this
            have hdep : H a (ind2 v1 v2) = H a (ind1 v1) := hDep a haA _ _ (fun i hi => by
              have : i ≠ v2 := fun h => h2na (h ▸ hi); simp [ind2, ind1, this])
            rw [hdep] at this; cases h : H a (ind1 v1)
            · rw [h] at this; simp at this
            · rfl
          have hb4 : H b (ind1 v4) = true := by
            have := hAnd (ind2 v3 v4); rw [ht34] at this
            have hdep : H b (ind2 v3 v4) = H b (ind1 v4) := hDep b hbA _ _ (fun i hi => by
              have : i ≠ v3 := fun h => h3nb (h ▸ hi); simp [ind2, ind1, this])
            rw [hdep] at this; cases h : H b (ind1 v4)
            · rw [h] at this; simp at this
            · rfl
          have ha14 : H a (ind2 v1 v4) = H a (ind1 v1) := hDep a haA _ _ (fun i hi => by
            have : i ≠ v4 := fun h => h4na (h ▸ hi); simp [ind2, ind1, this])
          have hb14 : H b (ind2 v1 v4) = H b (ind1 v4) := hDep b hbA _ _ (fun i hi => by
            have : i ≠ v1 := fun h => h1nb (h ▸ hi); simp [ind2, ind1, this])
          have h14t := hAnd (ind2 v1 v4)
          rw [hf14, ha14, hb14, ha1, hb4] at h14t; simp at h14t
        · have h1na : v1.val ∉ S a := Finset.disjoint_right.mp hDisj h1b
          have h3na : v3.val ∉ S a := Finset.disjoint_right.mp hDisj h3b
          have h2nb : v2.val ∉ S b := Finset.disjoint_left.mp hDisj h2a
          have h4nb : v4.val ∉ S b := Finset.disjoint_left.mp hDisj h4a
          have hb1 : H b (ind1 v1) = true := by
            have := hAnd (ind2 v1 v2); rw [ht12] at this
            have hdep : H b (ind2 v1 v2) = H b (ind1 v1) := hDep b hbA _ _ (fun i hi => by
              have : i ≠ v2 := fun h => h2nb (h ▸ hi); simp [ind2, ind1, this])
            rw [hdep] at this; cases h : H b (ind1 v1)
            · rw [h] at this; simp at this
            · rfl
          have ha4 : H a (ind1 v4) = true := by
            have := hAnd (ind2 v3 v4); rw [ht34] at this
            have hdep : H a (ind2 v3 v4) = H a (ind1 v4) := hDep a haA _ _ (fun i hi => by
              have : i ≠ v3 := fun h => h3na (h ▸ hi); simp [ind2, ind1, this])
            rw [hdep] at this; cases h : H a (ind1 v4)
            · rw [h] at this; simp at this
            · rfl
          have ha14 : H a (ind2 v1 v4) = H a (ind1 v4) := hDep a haA _ _ (fun i hi => by
            have : i ≠ v1 := fun h => h1na (h ▸ hi); simp [ind2, ind1, this])
          have hb14 : H b (ind2 v1 v4) = H b (ind1 v1) := hDep b hbA _ _ (fun i hi => by
            have : i ≠ v4 := fun h => h4nb (h ▸ hi); simp [ind2, ind1, this])
          have h14t := hAnd (ind2 v1 v4)
          rw [hf14, ha14, hb14, ha4, hb1] at h14t; simp at h14t
      · rcases hmemAB v1 hv1 with h1a | h1b <;>
        rcases hmemAB v2 hv2 with h2a | h2b <;>
        rcases hmemAB v3 hv3 with h3a | h3b <;>
        rcases hmemAB v4 hv4 with h4a | h4b
        all_goals
          try exact hOrCross v1 v2 hOr hf1 hf2 ht12 (Or.inl ⟨‹_›, ‹_›⟩)
          try exact hOrCross v1 v2 hOr hf1 hf2 ht12 (Or.inr ⟨‹_›, ‹_›⟩)
          try exact hOrCross v2 v3 hOr hf2 hf3 ht23 (Or.inl ⟨‹_›, ‹_›⟩)
          try exact hOrCross v2 v3 hOr hf2 hf3 ht23 (Or.inr ⟨‹_›, ‹_›⟩)
          try exact hOrCross v3 v4 hOr hf3 hf4 ht34 (Or.inl ⟨‹_›, ‹_›⟩)
          try exact hOrCross v3 v4 hOr hf3 hf4 ht34 (Or.inr ⟨‹_›, ‹_›⟩)
        · exact hNotEmptySide b a hbA haA haw (Or.inr (fun x => by rw [hOr, Bool.or_comm]))
            ⟨Finset.disjoint_left.mp hDisj h1a, Finset.disjoint_left.mp hDisj h2a,
             Finset.disjoint_left.mp hDisj h3a, Finset.disjoint_left.mp hDisj h4a⟩
        · exact hNotEmptySide a b haA hbA hbw (Or.inr hOr)
            ⟨Finset.disjoint_right.mp hDisj h1b, Finset.disjoint_right.mp hDisj h2b,
             Finset.disjoint_right.mp hDisj h3b, Finset.disjoint_right.mp hDisj h4b⟩

/-! ## Edge bound for P4-free induced bipartite subgraphs -/

lemma card_edges_of_no_P4 {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (P L : Finset (Fin N))
    (hNoP4 : ∀ p1 ∈ P, ∀ p2 ∈ P, p1 ≠ p2 → ∀ l1 ∈ L, ∀ l2 ∈ L, l1 ≠ l2 →
      ¬ (I p1 l1 ∧ I p2 l1 ∧ I p2 l2)) :
    ((P ×ˢ L).filter (fun pl => I pl.1 pl.2)).card ≤ P.card + L.card := by
  set E := (P ×ˢ L).filter (fun pl => I pl.1 pl.2)
  set EP := E.filter (fun pl => (L.filter (fun l => I pl.1 l)).card = 1)
  set EL := E.filter (fun pl => (P.filter (fun p => I p pl.2)).card = 1)
  have hSub : E ⊆ EP ∪ EL := by
    intro ⟨p, l⟩ hpl
    rw [Finset.mem_union]
    have hmem := Finset.mem_filter.mp hpl
    have hpP : p ∈ P := (Finset.mem_product.mp hmem.1).1
    have hlL : l ∈ L := (Finset.mem_product.mp hmem.1).2
    have hI : I p l := hmem.2
    have hdp_pos : 1 ≤ (L.filter (fun l' => I p l')).card :=
      Finset.card_pos.mpr ⟨l, Finset.mem_filter.mpr ⟨hlL, hI⟩⟩
    have hdl_pos : 1 ≤ (P.filter (fun p' => I p' l)).card :=
      Finset.card_pos.mpr ⟨p, Finset.mem_filter.mpr ⟨hpP, hI⟩⟩
    by_cases hdp : (L.filter (fun l' => I p l')).card = 1
    · exact Or.inl (Finset.mem_filter.mpr ⟨hpl, hdp⟩)
    · right
      apply Finset.mem_filter.mpr
      refine ⟨hpl, ?_⟩
      by_contra hdl
      dsimp only at hdl
      have hdp2 : 1 < (L.filter (fun l' => I p l')).card := by omega
      have hdl2 : 1 < (P.filter (fun p' => I p' l)).card := by omega
      obtain ⟨l2, hl2m, hl2ne⟩ := Finset.exists_mem_ne hdp2 l
      obtain ⟨p1, hp1m, hp1ne⟩ := Finset.exists_mem_ne hdl2 p
      have hl2 := Finset.mem_filter.mp hl2m
      have hp1 := Finset.mem_filter.mp hp1m
      exact hNoP4 p1 hp1.1 p hpP hp1ne l hlL l2 hl2.1 hl2ne.symm ⟨hp1.2, hI, hl2.2⟩
  have hEP : EP.card ≤ P.card := by
    have hinj : Set.InjOn Prod.fst (EP : Set (Fin N × Fin N)) := by
      intro ⟨p1, l1⟩ h1 ⟨p2, l2⟩ h2 hfst
      dsimp only at hfst; subst hfst
      have hm1 := Finset.mem_filter.mp h1
      have hm2 := Finset.mem_filter.mp h2
      have hcard1 : (L.filter (fun l => I p1 l)).card = 1 := hm1.2
      have hl1 : l1 ∈ L.filter (fun l => I p1 l) :=
        Finset.mem_filter.mpr ⟨(Finset.mem_product.mp (Finset.mem_filter.mp hm1.1).1).2, (Finset.mem_filter.mp hm1.1).2⟩
      have hl2 : l2 ∈ L.filter (fun l => I p1 l) :=
        Finset.mem_filter.mpr ⟨(Finset.mem_product.mp (Finset.mem_filter.mp hm2.1).1).2, (Finset.mem_filter.mp hm2.1).2⟩
      have heq := Finset.card_le_one.mp (le_of_eq hcard1) l1 hl1 l2 hl2
      exact Prod.ext rfl heq
    calc EP.card = (EP.image Prod.fst).card := (Finset.card_image_of_injOn hinj).symm
      _ ≤ P.card := Finset.card_le_card (fun p hp => by
          obtain ⟨⟨p', l'⟩, hmem, rfl⟩ := Finset.mem_image.mp hp
          exact (Finset.mem_product.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hmem).1).1).1)
  have hEL : EL.card ≤ L.card := by
    have hinj : Set.InjOn Prod.snd (EL : Set (Fin N × Fin N)) := by
      intro ⟨p1, l1⟩ h1 ⟨p2, l2⟩ h2 hsnd
      dsimp only at hsnd; subst hsnd
      have hm1 := Finset.mem_filter.mp h1
      have hm2 := Finset.mem_filter.mp h2
      have hcard1 : (P.filter (fun p => I p l1)).card = 1 := hm1.2
      have hp1 : p1 ∈ P.filter (fun p => I p l1) :=
        Finset.mem_filter.mpr ⟨(Finset.mem_product.mp (Finset.mem_filter.mp hm1.1).1).1, (Finset.mem_filter.mp hm1.1).2⟩
      have hp2 : p2 ∈ P.filter (fun p => I p l1) :=
        Finset.mem_filter.mpr ⟨(Finset.mem_product.mp (Finset.mem_filter.mp hm2.1).1).1, (Finset.mem_filter.mp hm2.1).2⟩
      have heq := Finset.card_le_one.mp (le_of_eq hcard1) p1 hp1 p2 hp2
      exact Prod.ext heq rfl
    calc EL.card = (EL.image Prod.snd).card := (Finset.card_image_of_injOn hinj).symm
      _ ≤ L.card := Finset.card_le_card (fun l hl => by
          obtain ⟨⟨p', l'⟩, hmem, rfl⟩ := Finset.mem_image.mp hl
          exact (Finset.mem_product.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hmem).1).1).2)
  calc E.card ≤ (EP ∪ EL).card := Finset.card_le_card hSub
    _ ≤ EP.card + EL.card := Finset.card_union_le EP EL
    _ ≤ P.card + L.card := Nat.add_le_add hEP hEL

/-! ## Main lower bound: no IsAO2 circuit of size ≤ 2 * N computes PG(2, q) -/

theorem no_small_circuit {q N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 201 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hCard : ∀ l : Fin N, Fintype.card { p : Fin N // I p l } = q + 1)
    (hUniq : ∀ p1 p2 : Fin N, p1 ≠ p2 → ∃! l : Fin N, I p1 l ∧ I p2 l)
    (C : Circuit) (hAO : IsAO2 (N + N) C)
    (hEval : ∀ x : Fin (N + N) → Bool,
      circuitFun (N + N) C x =
        decide (∃ p l : Fin N, I p l ∧ x (Fin.castAdd N p) = true ∧ x (Fin.natAdd N l) = true))
    (hSize : C.size ≤ 2 * N) : False := by
  have hNpos : 2 ≤ N := by nlinarith
  have hrb := hAO.2.1
  have hf_zero : wval C (zeroIn (n := N + N)) C.output = false := by
    have h := hEval zeroIn
    simp only [circuitFun, Circuit.eval, zeroIn, Bool.false_eq_true, and_false, exists_false,
      decide_false] at h
    exact h
  have hf_ind1 : ∀ u : Fin (N + N), wval C (ind1 u) C.output = false := by
    intro u
    have h := hEval (ind1 u)
    rw [show circuitFun (N + N) C (ind1 u) = wval C (ind1 u) C.output from rfl] at h
    rw [h]
    simp only [decide_eq_false_iff_not, not_exists, not_and]
    intro p l _ hp hl
    simp only [ind1, decide_eq_true_eq] at hp hl
    have : (Fin.castAdd N p : Fin (N + N)).val = (Fin.natAdd N l : Fin (N + N)).val :=
      congrArg Fin.val (hp.trans hl.symm)
    simp only [Fin.val_castAdd, Fin.val_natAdd] at this
    omega
  have hf_ind2_pl : ∀ (p l : Fin N),
      wval C (ind2 (Fin.castAdd N p) (Fin.natAdd N l)) C.output = decide (I p l) := by
    intro p l
    have h := hEval (ind2 (Fin.castAdd N p) (Fin.natAdd N l))
    rw [show circuitFun (N + N) C _ = wval C _ C.output from rfl] at h
    rw [h]
    congr 1
    apply propext
    constructor
    · rintro ⟨p', l', hI', hp', hl'⟩
      simp only [ind2, decide_eq_true_eq] at hp' hl'
      have hp_eq : p' = p := by
        rcases hp' with h1 | h1
        · exact Fin.ext (by simpa using congrArg Fin.val h1)
        · exfalso; have := congrArg Fin.val h1; simp at this; omega
      have hl_eq : l' = l := by
        rcases hl' with h1 | h1
        · exfalso; have := congrArg Fin.val h1; simp at this; omega
        · exact Fin.ext (by simpa using congrArg Fin.val h1)
      subst hp_eq; subst hl_eq; exact hI'
    · intro hI
      exact ⟨p, l, hI, by simp [ind2], by simp [ind2]⟩
  have hPtDeg : ∀ p : Fin N, ∃ l : Fin N, I p l := by
    intro p
    have hne : ∃ p' : Fin N, p ≠ p' := by
      by_cases h0 : p.val = 0
      · exact ⟨⟨1, by omega⟩, fun h => by have := congrArg Fin.val h; dsimp at this; omega⟩
      · exact ⟨⟨0, by omega⟩, fun h => by have := congrArg Fin.val h; dsimp at this; omega⟩
    obtain ⟨p', hpp'⟩ := hne
    obtain ⟨l, ⟨hpl, _⟩, _⟩ := hUniq p p' hpp'
    exact ⟨l, hpl⟩
  have hLnDeg : ∀ l : Fin N, ∃ p : Fin N, I p l := by
    intro l
    have hpos : 0 < Fintype.card { p : Fin N // I p l } := by rw [hCard l]; omega
    obtain ⟨⟨p, hp⟩⟩ := Fintype.card_pos_iff.mp hpos
    exact ⟨p, hp⟩
  have hInCone : ∀ i : Fin (N + N), i.val ∈ cone (N + N) C C.output := by
    intro i
    by_contra hi
    by_cases hlt : i.val < N
    · set p : Fin N := ⟨i.val, hlt⟩
      have hi_eq : i = Fin.castAdd N p := Fin.ext rfl
      obtain ⟨l, hpl⟩ := hPtDeg p
      have heq : wval C (ind2 (Fin.castAdd N p) (Fin.natAdd N l)) C.output =
          wval C (ind1 (Fin.natAdd N l)) C.output := by
        apply wval_eq_of_cone C hAO
        intro j hj
        have hji : j ≠ Fin.castAdd N p := fun h => hi (by rw [hi_eq]; exact h ▸ hj)
        simp only [ind2, ind1, hji, false_or]
      rw [hf_ind2_pl p l, hf_ind1] at heq
      simp [hpl] at heq
    · set l : Fin N := ⟨i.val - N, by omega⟩
      have hi_eq : i = Fin.natAdd N l := Fin.ext (by dsimp [l]; omega)
      obtain ⟨p, hpl⟩ := hLnDeg l
      have heq : wval C (ind2 (Fin.castAdd N p) (Fin.natAdd N l)) C.output =
          wval C (ind1 (Fin.castAdd N p)) C.output := by
        apply wval_eq_of_cone C hAO
        intro j hj
        have hji : j ≠ Fin.natAdd N l := fun h => hi (by rw [hi_eq]; exact h ▸ hj)
        simp only [ind2, ind1, hji, or_false]
      rw [hf_ind2_pl p l, hf_ind1] at heq
      simp [hpl] at heq
  have hOutGe : N + N ≤ C.output := by
    by_contra hlt
    have h0 : (⟨0, by omega⟩ : Fin (N + N)).val ∈ cone (N + N) C C.output := hInCone ⟨0, by omega⟩
    have h1 : (⟨1, by omega⟩ : Fin (N + N)).val ∈ cone (N + N) C C.output := hInCone ⟨1, by omega⟩
    rw [mem_cone_iff_of_not_gate C (by omega)] at h0 h1
    dsimp at h0 h1
    omega
  have hOutLt : C.output < (N + N) + C.gates.length := by
    by_contra hge
    obtain ⟨l, hpl⟩ := hPtDeg ⟨0, by omega⟩
    have h1 := hf_ind2_pl ⟨0, by omega⟩ l
    rw [wval_ge C _ (by omega)] at h1
    simp [hpl] at h1
  set coneOut := cone (N + N) C C.output
  set L := coneOut.filter (fun g => N + N ≤ g)
  set Wneed := coneOut.erase C.output
  have hLgates : ∀ g ∈ L, N + N ≤ g ∧ g - (N + N) < C.gates.length := by
    intro g hg
    have hm := Finset.mem_filter.mp hg
    have hle := mem_cone_le (N + N) C hrb C.output g hm.1
    exact ⟨hm.2, by omega⟩
  set r : ℕ → ℕ := fun u => ∑ g ∈ L, (gateAt C (g - (N + N))).inputs.count u
  have hr_pos : ∀ u ∈ Wneed, 1 ≤ r u := by
    intro u hu
    have hmem := Finset.mem_erase.mp hu
    have hle := mem_cone_le (N + N) C hrb C.output u hmem.2
    have hlt : u < C.output := lt_of_le_of_ne hle hmem.1
    obtain ⟨g, hgC, hg1, _, hgu⟩ := exists_reader_of_mem_cone (N + N) C hrb C.output u hmem.2 hlt
    have hgL : g ∈ L := Finset.mem_filter.mpr ⟨hgC, hg1⟩
    have hcnt : 1 ≤ (gateAt C (g - (N + N))).inputs.count u := List.count_pos_iff.mpr hgu
    exact le_trans hcnt (Finset.single_le_sum (f := fun g => (gateAt C (g - (N + N))).inputs.count u)
      (fun _ _ => Nat.zero_le _) hgL)
  have hr_sum : ∑ u ∈ Wneed, r u = 2 * L.card := by
    calc ∑ u ∈ Wneed, r u
        = ∑ g ∈ L, ∑ u ∈ Wneed, (gateAt C (g - (N + N))).inputs.count u := Finset.sum_comm
      _ = ∑ g ∈ L, (gateAt C (g - (N + N))).inputs.length := by
          apply Finset.sum_congr rfl
          intro g hg
          have hgP := hLgates g hg
          have hsub : ∀ u ∈ (gateAt C (g - (N + N))).inputs, u ∈ Wneed := by
            intro u hu
            have hult : u < g := by have := hrb (g - (N + N)) hgP.2 u hu; omega
            have hgle : g ≤ C.output := mem_cone_le (N + N) C hrb C.output g (Finset.mem_filter.mp hg).1
            have huC : u ∈ coneOut :=
              cone_subset_of_mem (N + N) C hrb C.output g (Finset.mem_filter.mp hg).1
                (mem_cone_of_input (N + N) C hrb hgP.1 hgP.2 hu)
            exact Finset.mem_erase.mpr ⟨by omega, huC⟩
          have hgen : ∀ (xs : List ℕ), (∀ u ∈ xs, u ∈ Wneed) →
              ∑ u ∈ Wneed, xs.count u = xs.length := by
            intro xs
            induction xs with
            | nil => intro _; simp
            | cons x xs ih =>
              intro hx
              simp only [List.count_cons, Finset.sum_add_distrib, List.length_cons]
              have hxW : x ∈ Wneed := hx x (by simp)
              have h1 : ∑ u ∈ Wneed, (if x == u then 1 else 0) = 1 := by
                have : (fun u => if x == u then 1 else 0) = (fun u => if u = x then 1 else 0) := by
                  funext u
                  by_cases h : u = x
                  · subst h; simp
                  · have h' : x ≠ u := Ne.symm h; simp [h, h']
                rw [this, Finset.sum_ite_eq']
                simp [hxW]
              rw [ih (fun u hu => hx u (by simp [hu])), h1]
          exact hgen _ hsub
      _ = ∑ _g ∈ L, 2 := by
          apply Finset.sum_congr rfl
          intro g hg
          have hgP := hLgates g hg
          apply hAO.2.2
          unfold gateAt
          rw [List.getD_eq_getElem _ _ hgP.2]
          exact List.getElem_mem hgP.2
      _ = 2 * L.card := by simp [mul_comm]
  have hConeOut_card : coneOut.card = (N + N) + L.card := by
    have hEq : coneOut = Finset.range (N + N) ∪ L := by
      ext w
      simp only [Finset.mem_union, Finset.mem_range, L, Finset.mem_filter]
      constructor
      · intro hw
        by_cases h : w < N + N
        · exact Or.inl h
        · exact Or.inr ⟨hw, by omega⟩
      · rintro (h | ⟨hw, _⟩)
        · exact hInCone ⟨w, h⟩
        · exact hw
    have hDisj : Disjoint (Finset.range (N + N)) L := by
      rw [Finset.disjoint_left]
      intro w hw1 hw2
      have h1 := Finset.mem_range.mp hw1
      have h2 := (Finset.mem_filter.mp hw2).2
      omega
    rw [hEq, Finset.card_union_of_disjoint hDisj, Finset.card_range]
  have hWneed_card : Wneed.card = (N + N) + L.card - 1 := by
    rw [Finset.card_erase_of_mem (mem_cone_self (N + N) C C.output), hConeOut_card]
  have hL_le_n : L.card ≤ N + N := by
    have hinj : Set.InjOn (fun g => g - (N + N)) (L : Set ℕ) := by
      intro g1 hg1 g2 hg2 heq
      dsimp only at heq
      have h1 := (hLgates g1 hg1).1
      have h2 := (hLgates g2 hg2).1
      omega
    have hsub : L.image (fun g => g - (N + N)) ⊆ Finset.range C.gates.length := by
      intro j hj
      obtain ⟨g, hgL, rfl⟩ := Finset.mem_image.mp hj
      exact Finset.mem_range.mpr (hLgates g hgL).2
    calc L.card = (L.image (fun g => g - (N + N))).card := (Finset.card_image_of_injOn hinj).symm
      _ ≤ (Finset.range C.gates.length).card := Finset.card_le_card hsub
      _ = C.size := by simp [Circuit.size]
      _ ≤ 2 * N := hSize
      _ = N + N := by omega
  have hExcess : ∑ u ∈ Wneed, (r u - 1) ≤ 1 := by
    have hsum1 : ∑ u ∈ Wneed, (r u - 1) + Wneed.card = ∑ u ∈ Wneed, r u := by
      have : ∑ u ∈ Wneed, (r u - 1 + 1) = ∑ u ∈ Wneed, r u := by
        apply Finset.sum_congr rfl
        intro u hu
        have := hr_pos u hu; omega
      rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one] at this
      exact this
    omega
  have hExStar : ∃ wStar ∈ Wneed, ∀ u ∈ Wneed, u ≠ wStar → r u = 1 := by
    by_cases hAll : ∀ u ∈ Wneed, r u = 1
    · refine ⟨0, Finset.mem_erase.mpr ⟨by omega, hInCone ⟨0, by omega⟩⟩, fun u hu _ => hAll u hu⟩
    · push Not at hAll
      obtain ⟨wStar, hwW, hrne⟩ := hAll
      have hrge2 : 2 ≤ r wStar := by have := hr_pos wStar hwW; omega
      refine ⟨wStar, hwW, fun u hu hne => ?_⟩
      have h2 : (r wStar - 1) + (r u - 1) ≤ ∑ v ∈ Wneed, (r v - 1) := by
        have hsub : ({wStar, u} : Finset ℕ) ⊆ Wneed := by
          intro v hv; simp at hv; rcases hv with rfl | rfl <;> assumption
        have hsum_pair : ∑ v ∈ ({wStar, u} : Finset ℕ), (r v - 1) = (r wStar - 1) + (r u - 1) :=
          Finset.sum_pair hne.symm
        rw [← hsum_pair]
        exact Finset.sum_le_sum_of_subset hsub
      have := hr_pos u hu
      omega
  obtain ⟨wStar, hwStarW, hr_one⟩ := hExStar
  have hwStarC : wStar ∈ coneOut := (Finset.mem_erase.mp hwStarW).2
  have hwStar_lt : wStar < C.output :=
    lt_of_le_of_ne (mem_cone_le (N + N) C hrb C.output wStar hwStarC) (Finset.mem_erase.mp hwStarW).1
  have hOut_not_star : C.output ∉ cone (N + N) C wStar := by
    intro hmem
    have := mem_cone_le (N + N) C hrb wStar C.output hmem
    omega
  have hr_ge_two_of_ne : ∀ u g1 g2, g1 ∈ L → g2 ∈ L → g1 ≠ g2 →
      u ∈ (gateAt C (g1 - (N + N))).inputs → u ∈ (gateAt C (g2 - (N + N))).inputs → 2 ≤ r u := by
    intro u g1 g2 hg1 hg2 hne hu1 hu2
    have hsub : ({g1, g2} : Finset ℕ) ⊆ L := by
      intro g hg; simp at hg; rcases hg with rfl | rfl <;> assumption
    have h1 : 1 ≤ (gateAt C (g1 - (N + N))).inputs.count u := List.count_pos_iff.mpr hu1
    have h2 : 1 ≤ (gateAt C (g2 - (N + N))).inputs.count u := List.count_pos_iff.mpr hu2
    have hpair : ∑ g ∈ ({g1, g2} : Finset ℕ), (gateAt C (g - (N + N))).inputs.count u =
        (gateAt C (g1 - (N + N))).inputs.count u + (gateAt C (g2 - (N + N))).inputs.count u :=
      Finset.sum_pair hne
    calc 2 ≤ (gateAt C (g1 - (N + N))).inputs.count u + (gateAt C (g2 - (N + N))).inputs.count u := by omega
      _ = ∑ g ∈ ({g1, g2} : Finset ℕ), (gateAt C (g - (N + N))).inputs.count u := hpair.symm
      _ ≤ r u := Finset.sum_le_sum_of_subset hsub
  have hInput_outside : ∀ g ∈ L, g ∉ cone (N + N) C wStar →
      ∀ u ∈ (gateAt C (g - (N + N))).inputs, u = wStar ∨ u ∉ cone (N + N) C wStar := by
    intro g hgL hgNot u hu
    by_cases heq : u = wStar
    · exact Or.inl heq
    · right
      intro huStar
      have hult : u < wStar := lt_of_le_of_ne (mem_cone_le (N + N) C hrb wStar u huStar) heq
      obtain ⟨g', hg'Star, hg'1, _, hg'u⟩ := exists_reader_of_mem_cone (N + N) C hrb wStar u huStar hult
      have hg'L : g' ∈ L := Finset.mem_filter.mpr
        ⟨cone_subset_of_mem (N + N) C hrb C.output wStar hwStarC hg'Star, hg'1⟩
      have hne : g ≠ g' := fun h => hgNot (h ▸ hg'Star)
      have huW : u ∈ Wneed := Finset.mem_erase.mpr
        ⟨by omega, cone_subset_of_mem (N + N) C hrb C.output wStar hwStarC huStar⟩
      have h2 := hr_ge_two_of_ne u g g' hgL hg'L hne hu hg'u
      have h1 := hr_one u huW heq
      omega
  have hCone_inter : ∀ g ∈ L,
      let a := (gateAt C (g - (N + N))).inputs.getD 0 0
      let b := (gateAt C (g - (N + N))).inputs.getD 1 0
      ∀ z ∈ cone (N + N) C a ∩ cone (N + N) C b, z ∈ cone (N + N) C wStar := by
    intro g hgL a b z hz
    by_contra hzNot
    set bad := (cone (N + N) C a ∩ cone (N + N) C b) \ cone (N + N) C wStar
    have hbad_ne : bad.Nonempty := ⟨z, Finset.mem_sdiff.mpr ⟨hz, hzNot⟩⟩
    set m := bad.max' hbad_ne
    have hm_mem := Finset.mem_sdiff.mp (Finset.max'_mem bad hbad_ne)
    have hm_a : m ∈ cone (N + N) C a := (Finset.mem_inter.mp hm_mem.1).1
    have hm_b : m ∈ cone (N + N) C b := (Finset.mem_inter.mp hm_mem.1).2
    have hm_not : m ∉ cone (N + N) C wStar := hm_mem.2
    have hm_ne_star : m ≠ wStar := fun h => hm_not (h ▸ mem_cone_self (N + N) C wStar)
    have hgP := hLgates g hgL
    have hlen2 : (gateAt C (g - (N + N))).inputs.length = 2 := by
      apply hAO.2.2; unfold gateAt; rw [List.getD_eq_getElem _ _ hgP.2]; exact List.getElem_mem hgP.2
    have hlist : (gateAt C (g - (N + N))).inputs = [a, b] := by
      rcases hl : (gateAt C (g - (N + N))).inputs with _ | ⟨x, _ | ⟨y, _ | _⟩⟩ <;>
        simp [hl] at hlen2
      simp [a, b, hl]
    have ha_lt : a < g := by have := hrb (g - (N + N)) hgP.2 a (by rw [hlist]; simp); omega
    have hb_lt : b < g := by have := hrb (g - (N + N)) hgP.2 b (by rw [hlist]; simp); omega
    have hm_le_a : m ≤ a := mem_cone_le (N + N) C hrb a m hm_a
    have hm_le_b : m ≤ b := mem_cone_le (N + N) C hrb b m hm_b
    have hm_lt_out : m < C.output := by
      have := mem_cone_le (N + N) C hrb C.output g (Finset.mem_filter.mp hgL).1; omega
    have hm_W : m ∈ Wneed := Finset.mem_erase.mpr
      ⟨by omega, cone_subset_of_mem (N + N) C hrb C.output g (Finset.mem_filter.mp hgL).1
        (cone_subset_of_mem (N + N) C hrb g a (mem_cone_of_input (N + N) C hrb hgP.1 hgP.2 (by rw [hlist]; simp)) hm_a)⟩
    have hm_r1 : r m = 1 := hr_one m hm_W hm_ne_star
    by_cases hma : m = a
    · by_cases hmb : m = b
      · have hcnt : (gateAt C (g - (N + N))).inputs.count m = 2 := by rw [hlist, ← hma, ← hmb]; simp
        have h2 : 2 ≤ r m := by
          rw [← hcnt]
          exact Finset.single_le_sum (f := fun g' => (gateAt C (g' - (N + N))).inputs.count m)
            (fun _ _ => Nat.zero_le _) hgL
        omega
      · have hmlt : m < b := lt_of_le_of_ne hm_le_b hmb
        obtain ⟨g2, hg2b, hg2_1, _, hg2m⟩ := exists_reader_of_mem_cone (N + N) C hrb b m hm_b hmlt
        have hg2L : g2 ∈ L := Finset.mem_filter.mpr
          ⟨cone_subset_of_mem (N + N) C hrb C.output g (Finset.mem_filter.mp hgL).1
            (cone_subset_of_mem (N + N) C hrb g b (mem_cone_of_input (N + N) C hrb hgP.1 hgP.2 (by rw [hlist]; simp)) hg2b), hg2_1⟩
        have hg2le : g2 ≤ b := mem_cone_le (N + N) C hrb b g2 hg2b
        have h2 := hr_ge_two_of_ne m g g2 hgL hg2L (by omega) (by rw [hlist, hma]; simp) hg2m
        omega
    · by_cases hmb : m = b
      · have hmlt : m < a := lt_of_le_of_ne hm_le_a hma
        obtain ⟨g1, hg1a, hg1_1, _, hg1m⟩ := exists_reader_of_mem_cone (N + N) C hrb a m hm_a hmlt
        have hg1L : g1 ∈ L := Finset.mem_filter.mpr
          ⟨cone_subset_of_mem (N + N) C hrb C.output g (Finset.mem_filter.mp hgL).1
            (cone_subset_of_mem (N + N) C hrb g a (mem_cone_of_input (N + N) C hrb hgP.1 hgP.2 (by rw [hlist]; simp)) hg1a), hg1_1⟩
        have hg1le : g1 ≤ a := mem_cone_le (N + N) C hrb a g1 hg1a
        have h2 := hr_ge_two_of_ne m g g1 hgL hg1L (by omega) (by rw [hlist, hmb]; simp) hg1m
        omega
      · have hmlta : m < a := lt_of_le_of_ne hm_le_a hma
        have hmltb : m < b := lt_of_le_of_ne hm_le_b hmb
        obtain ⟨g1, hg1a, hg1_1, hg1_2, hg1m⟩ := exists_reader_of_mem_cone (N + N) C hrb a m hm_a hmlta
        obtain ⟨g2, hg2b, hg2_1, _, hg2m⟩ := exists_reader_of_mem_cone (N + N) C hrb b m hm_b hmltb
        have hg1L : g1 ∈ L := Finset.mem_filter.mpr
          ⟨cone_subset_of_mem (N + N) C hrb C.output g (Finset.mem_filter.mp hgL).1
            (cone_subset_of_mem (N + N) C hrb g a (mem_cone_of_input (N + N) C hrb hgP.1 hgP.2 (by rw [hlist]; simp)) hg1a), hg1_1⟩
        have hg2L : g2 ∈ L := Finset.mem_filter.mpr
          ⟨cone_subset_of_mem (N + N) C hrb C.output g (Finset.mem_filter.mp hgL).1
            (cone_subset_of_mem (N + N) C hrb g b (mem_cone_of_input (N + N) C hrb hgP.1 hgP.2 (by rw [hlist]; simp)) hg2b), hg2_1⟩
        by_cases h12 : g1 = g2
        · subst h12
          have hm_lt_g1 : m < g1 := by have := hrb (g1 - (N + N)) hg1_2 m hg1m; omega
          have hg1_star : g1 ∈ cone (N + N) C wStar := by
            by_contra hnot
            have hg1_bad : g1 ∈ bad := Finset.mem_sdiff.mpr ⟨Finset.mem_inter.mpr ⟨hg1a, hg2b⟩, hnot⟩
            have hle := Finset.le_max' bad g1 hg1_bad
            omega
          exact hm_not (cone_subset_of_mem (N + N) C hrb wStar g1 hg1_star
            (mem_cone_of_input (N + N) C hrb hg1_1 hg1_2 hg1m))
        · have h2 := hr_ge_two_of_ne m g1 g2 hg1L hg2L h12 hg1m hg2m
          omega
  have hCone_disj_star : ∀ g ∈ L, g ∈ cone (N + N) C wStar →
      let a := (gateAt C (g - (N + N))).inputs.getD 0 0
      let b := (gateAt C (g - (N + N))).inputs.getD 1 0
      Disjoint (cone (N + N) C a) (cone (N + N) C b) := by
    intro g hgL hgStar a b
    rw [Finset.disjoint_left]
    intro z hza hzb
    set inter := cone (N + N) C a ∩ cone (N + N) C b
    have hne : inter.Nonempty := ⟨z, Finset.mem_inter.mpr ⟨hza, hzb⟩⟩
    set m := inter.max' hne
    have hm := Finset.mem_inter.mp (Finset.max'_mem inter hne)
    have hm_a := hm.1
    have hm_b := hm.2
    have hgP := hLgates g hgL
    have hlen2 : (gateAt C (g - (N + N))).inputs.length = 2 := by
      apply hAO.2.2; unfold gateAt; rw [List.getD_eq_getElem _ _ hgP.2]; exact List.getElem_mem hgP.2
    have hlist : (gateAt C (g - (N + N))).inputs = [a, b] := by
      rcases hl : (gateAt C (g - (N + N))).inputs with _ | ⟨x, _ | ⟨y, _ | _⟩⟩ <;>
        simp [hl] at hlen2
      simp [a, b, hl]
    have ha_lt : a < g := by have := hrb (g - (N + N)) hgP.2 a (by rw [hlist]; simp); omega
    have hb_lt : b < g := by have := hrb (g - (N + N)) hgP.2 b (by rw [hlist]; simp); omega
    have hm_le_a : m ≤ a := mem_cone_le (N + N) C hrb a m hm_a
    have hm_le_b : m ≤ b := mem_cone_le (N + N) C hrb b m hm_b
    have hg_le_star : g ≤ wStar := mem_cone_le (N + N) C hrb wStar g hgStar
    have hm_ne_star : m ≠ wStar := by omega
    have hm_W : m ∈ Wneed := Finset.mem_erase.mpr
      ⟨by omega, cone_subset_of_mem (N + N) C hrb C.output g (Finset.mem_filter.mp hgL).1
        (cone_subset_of_mem (N + N) C hrb g a (mem_cone_of_input (N + N) C hrb hgP.1 hgP.2 (by rw [hlist]; simp)) hm_a)⟩
    have hm_r1 : r m = 1 := hr_one m hm_W hm_ne_star
    by_cases hma : m = a
    · by_cases hmb : m = b
      · have hcnt : (gateAt C (g - (N + N))).inputs.count m = 2 := by rw [hlist, ← hma, ← hmb]; simp
        have h2 : 2 ≤ r m := by
          rw [← hcnt]
          exact Finset.single_le_sum (f := fun g' => (gateAt C (g' - (N + N))).inputs.count m)
            (fun _ _ => Nat.zero_le _) hgL
        omega
      · have hmlt : m < b := lt_of_le_of_ne hm_le_b hmb
        obtain ⟨g2, hg2b, hg2_1, _, hg2m⟩ := exists_reader_of_mem_cone (N + N) C hrb b m hm_b hmlt
        have hg2L : g2 ∈ L := Finset.mem_filter.mpr
          ⟨cone_subset_of_mem (N + N) C hrb C.output g (Finset.mem_filter.mp hgL).1
            (cone_subset_of_mem (N + N) C hrb g b (mem_cone_of_input (N + N) C hrb hgP.1 hgP.2 (by rw [hlist]; simp)) hg2b), hg2_1⟩
        have hg2le : g2 ≤ b := mem_cone_le (N + N) C hrb b g2 hg2b
        have h2 := hr_ge_two_of_ne m g g2 hgL hg2L (by omega) (by rw [hlist, hma]; simp) hg2m
        omega
    · by_cases hmb : m = b
      · have hmlt : m < a := lt_of_le_of_ne hm_le_a hma
        obtain ⟨g1, hg1a, hg1_1, _, hg1m⟩ := exists_reader_of_mem_cone (N + N) C hrb a m hm_a hmlt
        have hg1L : g1 ∈ L := Finset.mem_filter.mpr
          ⟨cone_subset_of_mem (N + N) C hrb C.output g (Finset.mem_filter.mp hgL).1
            (cone_subset_of_mem (N + N) C hrb g a (mem_cone_of_input (N + N) C hrb hgP.1 hgP.2 (by rw [hlist]; simp)) hg1a), hg1_1⟩
        have hg1le : g1 ≤ a := mem_cone_le (N + N) C hrb a g1 hg1a
        have h2 := hr_ge_two_of_ne m g g1 hgL hg1L (by omega) (by rw [hlist, hmb]; simp) hg1m
        omega
      · have hmlta : m < a := lt_of_le_of_ne hm_le_a hma
        have hmltb : m < b := lt_of_le_of_ne hm_le_b hmb
        obtain ⟨g1, hg1a, hg1_1, hg1_2, hg1m⟩ := exists_reader_of_mem_cone (N + N) C hrb a m hm_a hmlta
        obtain ⟨g2, hg2b, hg2_1, _, hg2m⟩ := exists_reader_of_mem_cone (N + N) C hrb b m hm_b hmltb
        have hg1L : g1 ∈ L := Finset.mem_filter.mpr
          ⟨cone_subset_of_mem (N + N) C hrb C.output g (Finset.mem_filter.mp hgL).1
            (cone_subset_of_mem (N + N) C hrb g a (mem_cone_of_input (N + N) C hrb hgP.1 hgP.2 (by rw [hlist]; simp)) hg1a), hg1_1⟩
        have hg2L : g2 ∈ L := Finset.mem_filter.mpr
          ⟨cone_subset_of_mem (N + N) C hrb C.output g (Finset.mem_filter.mp hgL).1
            (cone_subset_of_mem (N + N) C hrb g b (mem_cone_of_input (N + N) C hrb hgP.1 hgP.2 (by rw [hlist]; simp)) hg2b), hg2_1⟩
        by_cases h12 : g1 = g2
        · subst h12
          have hm_lt_g1 : m < g1 := by have := hrb (g1 - (N + N)) hg1_2 m hg1m; omega
          have hle := Finset.le_max' inter g1 (Finset.mem_inter.mpr ⟨hg1a, hg2b⟩)
          omega
        · have h2 := hr_ge_two_of_ne m g1 g2 hg1L hg2L h12 hg1m hg2m
          omega
  have hEvalMod_dep : ∀ c : Bool, ∀ w ∈ coneOut, w = wStar ∨ w ∉ cone (N + N) C wStar →
      ∀ x y : Fin (N + N) → Bool,
      (∀ i : Fin (N + N), i.val ∈ cone (N + N) C w \ cone (N + N) C wStar → x i = y i) →
      evalMod C wStar c x w = evalMod C wStar c y w := by
    intro c w
    induction w using Nat.strongRecOn with
    | ind w ih =>
      intro hwC hwGood x y hxy
      rw [evalMod, evalMod]
      by_cases hws : w = wStar
      · rw [if_pos hws, if_pos hws]
      · rw [if_neg hws, if_neg hws]
        by_cases hw : N + N ≤ w ∧ w - (N + N) < C.gates.length
        · rw [if_pos hw, if_pos hw]
          dsimp only
          have hwNot : w ∉ cone (N + N) C wStar := hwGood.resolve_left hws
          have hwL : w ∈ L := Finset.mem_filter.mpr ⟨hwC, hw.1⟩
          have hlen2 : (gateAt C (w - (N + N))).inputs.length = 2 := by
            apply hAO.2.2; unfold gateAt; rw [List.getD_eq_getElem _ _ hw.2]; exact List.getElem_mem hw.2
          have h0mem : (gateAt C (w - (N + N))).inputs.getD 0 0 ∈ (gateAt C (w - (N + N))).inputs := by
            rcases hl : (gateAt C (w - (N + N))).inputs with _ | ⟨a, _ | ⟨b, _ | _⟩⟩ <;> simp [hl] at hlen2 ⊢
          have h1mem : (gateAt C (w - (N + N))).inputs.getD 1 0 ∈ (gateAt C (w - (N + N))).inputs := by
            rcases hl : (gateAt C (w - (N + N))).inputs with _ | ⟨a, _ | ⟨b, _ | _⟩⟩ <;> simp [hl] at hlen2 ⊢
          have ha_lt : (gateAt C (w - (N + N))).inputs.getD 0 0 < w := by
            have := hrb (w - (N + N)) hw.2 _ h0mem; omega
          have hb_lt : (gateAt C (w - (N + N))).inputs.getD 1 0 < w := by
            have := hrb (w - (N + N)) hw.2 _ h1mem; omega
          have haC : (gateAt C (w - (N + N))).inputs.getD 0 0 ∈ coneOut :=
            cone_subset_of_mem (N + N) C hrb C.output w hwC (mem_cone_of_input (N + N) C hrb hw.1 hw.2 h0mem)
          have hbC : (gateAt C (w - (N + N))).inputs.getD 1 0 ∈ coneOut :=
            cone_subset_of_mem (N + N) C hrb C.output w hwC (mem_cone_of_input (N + N) C hrb hw.1 hw.2 h1mem)
          have haSub := cone_subset_of_mem (N + N) C hrb w _ (mem_cone_of_input (N + N) C hrb hw.1 hw.2 h0mem)
          have hbSub := cone_subset_of_mem (N + N) C hrb w _ (mem_cone_of_input (N + N) C hrb hw.1 hw.2 h1mem)
          have haGood := hInput_outside w hwL hwNot _ h0mem
          have hbGood := hInput_outside w hwL hwNot _ h1mem
          simp only [ha_lt, hb_lt, ↓reduceIte]
          have hva := ih _ ha_lt haC haGood x y (fun i hi =>
            hxy i (Finset.mem_sdiff.mpr ⟨haSub (Finset.mem_sdiff.mp hi).1, (Finset.mem_sdiff.mp hi).2⟩))
          have hvb := ih _ hb_lt hbC hbGood x y (fun i hi =>
            hxy i (Finset.mem_sdiff.mpr ⟨hbSub (Finset.mem_sdiff.mp hi).1, (Finset.mem_sdiff.mp hi).2⟩))
          rw [hva, hvb]
        · rw [if_neg hw, if_neg hw]
          split_ifs with hlt
          · have hwNot : w ∉ cone (N + N) C wStar := hwGood.resolve_left hws
            exact hxy ⟨w, hlt⟩ (Finset.mem_sdiff.mpr ⟨mem_cone_self (N + N) C w, hwNot⟩)
          · rfl
  set UP : Finset (Fin N) := Finset.univ.filter (fun p => (Fin.castAdd N p).val ∈ cone (N + N) C wStar)
  set VP : Finset (Fin N) := Finset.univ.filter (fun p => (Fin.castAdd N p).val ∉ cone (N + N) C wStar)
  set UL : Finset (Fin N) := Finset.univ.filter (fun l => (Fin.natAdd N l).val ∈ cone (N + N) C wStar)
  set VL : Finset (Fin N) := Finset.univ.filter (fun l => (Fin.natAdd N l).val ∉ cone (N + N) C wStar)
  -- 1. No P4 in V
  have hNoP4_V : ∀ p1 ∈ VP, ∀ p2 ∈ VP, p1 ≠ p2 → ∀ l1 ∈ VL, ∀ l2 ∈ VL, l1 ≠ l2 →
      ¬ (I p1 l1 ∧ I p2 l1 ∧ I p2 l2) := by
    intro p1 hp1 p2 hp2 hp12 l1 hl1 l2 hl2 hl12 ⟨h11, h21, h22⟩
    have hnot12 : ¬ I p1 l2 := by
      intro h12
      obtain ⟨l, _, huniq⟩ := hUniq p1 p2 hp12
      exact hl12 ((huniq l1 ⟨h11, h21⟩).trans (huniq l2 ⟨h12, h22⟩).symm)
    set c0 := wval C (zeroIn (n := N + N)) wStar
    set Av := coneOut.filter (fun w => w = wStar ∨ w ∉ cone (N + N) C wStar)
    set Hv := fun w (x : Fin (N + N) → Bool) => evalMod C wStar c0 x w
    set Sv := fun w => (cone (N + N) C w \ cone (N + N) C wStar).filter (· < N + N)
    have hno := no_P4 Av Hv Sv
      (fun w _ x y hxy => evalMod_mono C wStar (fun h => h) hxy w)
      (fun w hw x y hxy => hEvalMod_dep c0 w (Finset.mem_filter.mp hw).1 (Finset.mem_filter.mp hw).2 x y
        (fun i hi => hxy i (Finset.mem_filter.mpr ⟨hi, i.isLt⟩)))
      (fun w hw => by
        have hwC := (Finset.mem_filter.mp hw).1
        have hwGood := (Finset.mem_filter.mp hw).2
        by_cases hws : w = wStar
        · left; subst hws; simp [Sv]
        · have hwNot := hwGood.resolve_left hws
          by_cases hlt : w < N + N
          · right; left
            refine ⟨w, hlt, ?_⟩
            ext z
            simp only [Sv, Finset.mem_filter, Finset.mem_sdiff,
              mem_cone_iff_of_not_gate C (by omega : ¬ (N + N ≤ w ∧ w - (N + N) < C.gates.length)),
              Finset.mem_singleton]
            constructor
            · rintro ⟨⟨rfl, _⟩, _⟩; rfl
            · rintro rfl; exact ⟨⟨rfl, hwNot⟩, hlt⟩
          · right; right
            have hwL : w ∈ L := Finset.mem_filter.mpr ⟨hwC, by omega⟩
            have hwP := hLgates w hwL
            set a := (gateAt C (w - (N + N))).inputs.getD 0 0
            set b := (gateAt C (w - (N + N))).inputs.getD 1 0
            have hlen2 : (gateAt C (w - (N + N))).inputs.length = 2 := by
              apply hAO.2.2; unfold gateAt; rw [List.getD_eq_getElem _ _ hwP.2]; exact List.getElem_mem hwP.2
            have hlist : (gateAt C (w - (N + N))).inputs = [a, b] := by
              rcases hl : (gateAt C (w - (N + N))).inputs with _ | ⟨x, _ | ⟨y, _ | _⟩⟩ <;> simp [hl] at hlen2
              simp [a, b, hl]
            have ha_mem : a ∈ (gateAt C (w - (N + N))).inputs := by rw [hlist]; simp
            have hb_mem : b ∈ (gateAt C (w - (N + N))).inputs := by rw [hlist]; simp
            have ha_lt : a < w := by have := hrb (w - (N + N)) hwP.2 a ha_mem; omega
            have hb_lt : b < w := by have := hrb (w - (N + N)) hwP.2 b hb_mem; omega
            have haA : a ∈ Av := Finset.mem_filter.mpr
              ⟨cone_subset_of_mem (N + N) C hrb C.output w hwC (mem_cone_of_input (N + N) C hrb hwP.1 hwP.2 ha_mem),
               hInput_outside w hwL hwNot a ha_mem⟩
            have hbA : b ∈ Av := Finset.mem_filter.mpr
              ⟨cone_subset_of_mem (N + N) C hrb C.output w hwC (mem_cone_of_input (N + N) C hrb hwP.1 hwP.2 hb_mem),
               hInput_outside w hwL hwNot b hb_mem⟩
            refine ⟨a, haA, b, hbA, ha_lt, hb_lt, ?_, ?_, ?_⟩
            · rw [Finset.disjoint_left]
              intro z hza hzb
              have hza' := Finset.mem_sdiff.mp (Finset.mem_filter.mp hza).1
              have hzb' := Finset.mem_sdiff.mp (Finset.mem_filter.mp hzb).1
              exact hza'.2 (hCone_inter w hwL z (Finset.mem_inter.mpr ⟨hza'.1, hzb'.1⟩))
            · intro z hz
              have hzf := Finset.mem_filter.mp hz
              have hz' := Finset.mem_sdiff.mp hzf.1
              rw [mem_cone_iff_of_gate C hrb hwP.1 hwP.2] at hz'
              rcases hz'.1 with rfl | ⟨u, hu, hzu⟩
              · omega
              · rw [hlist] at hu
                simp at hu
                rcases hu with rfl | rfl
                · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hzu, hz'.2⟩, hzf.2⟩)
                · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hzu, hz'.2⟩, hzf.2⟩)
            · by_cases hop : (gateAt C (w - (N + N))).op = GateOp.and
              · left; intro x; dsimp only [Hv]; rw [evalMod]; dsimp only
                rw [if_neg hws, if_pos hwP, if_pos hop]
                dsimp only [a, b] at ha_lt hb_lt ⊢
                rw [if_pos ha_lt, if_pos hb_lt]
              · right; intro x; dsimp only [Hv]; rw [evalMod]; dsimp only
                rw [if_neg hws, if_pos hwP, if_neg hop]
                dsimp only [a, b] at ha_lt hb_lt ⊢
                rw [if_pos ha_lt, if_pos hb_lt])
      (v1 := Fin.castAdd N p1) (v2 := Fin.natAdd N l1) (v3 := Fin.castAdd N p2) (v4 := Fin.natAdd N l2)
      (fun h => by have := congrArg Fin.val h; simp at this; omega)
      (fun h => hp12 (Fin.ext (by simpa using congrArg Fin.val h)))
      (fun h => by have := congrArg Fin.val h; simp at this; omega)
      (fun h => by have := congrArg Fin.val h; simp at this; omega)
      (fun h => hl12 (Fin.ext (by simpa using congrArg Fin.val h)))
      (fun h => by have := congrArg Fin.val h; simp at this; omega)
      C.output (Finset.mem_filter.mpr ⟨mem_cone_self (N + N) C C.output, Or.inr hOut_not_star⟩)
    have hWstar_eq : ∀ x : Fin (N + N) → Bool,
        (∀ i : Fin (N + N), i.val ∈ cone (N + N) C wStar → x i = false) →
        Hv C.output x = wval C x C.output := by
      intro x hx
      have hws : wval C x wStar = c0 := wval_eq_of_cone C hAO wStar (fun i hi => by rw [hx i hi]; rfl)
      simp only [Hv, ← hws]
      exact evalMod_eq_wval C hAO wStar x C.output
    have hp1n : (Fin.castAdd N p1).val ∉ cone (N + N) C wStar := (Finset.mem_filter.mp hp1).2
    have hp2n : (Fin.castAdd N p2).val ∉ cone (N + N) C wStar := (Finset.mem_filter.mp hp2).2
    have hl1n : (Fin.natAdd N l1).val ∉ cone (N + N) C wStar := (Finset.mem_filter.mp hl1).2
    have hl2n : (Fin.natAdd N l2).val ∉ cone (N + N) C wStar := (Finset.mem_filter.mp hl2).2
    have h1 : ∀ u : Fin (N + N), u.val ∉ cone (N + N) C wStar → ∀ i : Fin (N + N), i.val ∈ cone (N + N) C wStar → ind1 u i = false := by
      intro u hu i hi; simp [ind1]; intro h; subst h; exact hu hi
    have h2 : ∀ u v : Fin (N + N), u.val ∉ cone (N + N) C wStar → v.val ∉ cone (N + N) C wStar →
        ∀ i : Fin (N + N), i.val ∈ cone (N + N) C wStar → ind2 u v i = false := by
      intro u v hu hv i hi; simp [ind2]; exact ⟨fun h => hu (h ▸ hi), fun h => hv (h ▸ hi)⟩
    apply hno
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hWstar_eq _ (h1 _ hp1n)]; exact hf_ind1 _
    · rw [hWstar_eq _ (h1 _ hl1n)]; exact hf_ind1 _
    · rw [hWstar_eq _ (h1 _ hp2n)]; exact hf_ind1 _
    · rw [hWstar_eq _ (h1 _ hl2n)]; exact hf_ind1 _
    · rw [hWstar_eq _ (h2 _ _ hp1n hl1n), hf_ind2_pl]; simp [h11]
    · rw [hWstar_eq _ (h2 _ _ hl1n hp2n)]
      rw [show ind2 (Fin.natAdd N l1) (Fin.castAdd N p2) = ind2 (Fin.castAdd N p2) (Fin.natAdd N l1) from
        by funext i; simp [ind2, or_comm]]
      rw [hf_ind2_pl]; simp [h21]
    · rw [hWstar_eq _ (h2 _ _ hp2n hl2n), hf_ind2_pl]; simp [h22]
    · rw [hWstar_eq _ (h2 _ _ hp1n hl2n), hf_ind2_pl]; simp [hnot12]
  -- 2. No P4 in U
  have hNoP4_U : ∀ p1 ∈ UP, ∀ p2 ∈ UP, p1 ≠ p2 → ∀ l1 ∈ UL, ∀ l2 ∈ UL, l1 ≠ l2 →
      ¬ (I p1 l1 ∧ I p2 l1 ∧ I p2 l2) := by
    intro p1 hp1 p2 hp2 hp12 l1 hl1 l2 hl2 hl12 ⟨h11, h21, h22⟩
    have hnot12 : ¬ I p1 l2 := by
      intro h12
      obtain ⟨l, _, huniq⟩ := hUniq p1 p2 hp12
      exact hl12 ((huniq l1 ⟨h11, h21⟩).trans (huniq l2 ⟨h12, h22⟩).symm)
    set ψ : Bool → Bool := fun b => evalMod C wStar b zeroIn C.output
    have hψ_eval : ∀ x : Fin (N + N) → Bool,
        (∀ i : Fin (N + N), i.val ∉ cone (N + N) C wStar → x i = false) →
        wval C x C.output = ψ (wval C x wStar) := by
      intro x hx
      rw [← evalMod_eq_wval C hAO wStar x C.output]
      exact hEvalMod_dep (wval C x wStar) C.output (mem_cone_self (N + N) C C.output) (Or.inr hOut_not_star) x zeroIn
        (fun i hi => by rw [hx i (Finset.mem_sdiff.mp hi).2]; rfl)
    have hψ_mono : ψ false = true → ψ true = true :=
      evalMod_mono C wStar (fun h => by cases h) (fun _ h => h) C.output
    have hp1u : (Fin.castAdd N p1).val ∈ cone (N + N) C wStar := (Finset.mem_filter.mp hp1).2
    have hp2u : (Fin.castAdd N p2).val ∈ cone (N + N) C wStar := (Finset.mem_filter.mp hp2).2
    have hl1u : (Fin.natAdd N l1).val ∈ cone (N + N) C wStar := (Finset.mem_filter.mp hl1).2
    have hl2u : (Fin.natAdd N l2).val ∈ cone (N + N) C wStar := (Finset.mem_filter.mp hl2).2
    have h1u : ∀ u : Fin (N + N), u.val ∈ cone (N + N) C wStar → ∀ i : Fin (N + N), i.val ∉ cone (N + N) C wStar → ind1 u i = false := by
      intro u hu i hi; simp [ind1]; intro h; subst h; exact hi hu
    have h2u : ∀ u v : Fin (N + N), u.val ∈ cone (N + N) C wStar → v.val ∈ cone (N + N) C wStar →
        ∀ i : Fin (N + N), i.val ∉ cone (N + N) C wStar → ind2 u v i = false := by
      intro u v hu hv i hi; simp [ind2]; exact ⟨fun h => hi (h ▸ hu), fun h => hi (h ▸ hv)⟩
    have hψ_f : ψ (wval C (zeroIn (n := N + N)) wStar) = false := by
      rw [← hψ_eval (zeroIn (n := N + N)) (fun _ _ => rfl)]; exact hf_zero
    have hψ_t : ψ (wval C (ind2 (Fin.castAdd N p1) (Fin.natAdd N l1)) wStar) = true := by
      rw [← hψ_eval _ (h2u _ _ hp1u hl1u), hf_ind2_pl]; simp [h11]
    have hψ_id : ∀ b : Bool, ψ b = b := by
      cases hf : ψ false <;> cases ht : ψ true
      · cases hb : wval C (ind2 (Fin.castAdd N p1) (Fin.natAdd N l1)) wStar
        · rw [hb, hf] at hψ_t; cases hψ_t
        · rw [hb, ht] at hψ_t; cases hψ_t
      · intro b; cases b <;> assumption
      · exfalso; have := hψ_mono hf; rw [ht] at this; cases this
      · cases hb : wval C (zeroIn (n := N + N)) wStar
        · rw [hb, hf] at hψ_f; cases hψ_f
        · rw [hb, ht] at hψ_f; cases hψ_f
    have hwStar_eq : ∀ x : Fin (N + N) → Bool,
        (∀ i : Fin (N + N), i.val ∉ cone (N + N) C wStar → x i = false) →
        wval C x wStar = wval C x C.output := fun x hx => by
      rw [hψ_eval x hx, hψ_id]
    set Au := cone (N + N) C wStar
    set Hu := fun w x => wval C x w
    set Su := fun w => (cone (N + N) C w).filter (· < N + N)
    have hno := no_P4 Au Hu Su
      (fun w _ x y hxy => wval_mono C hAO hxy w)
      (fun w _ x y hxy => wval_eq_of_cone C hAO w (fun i hi => hxy i (Finset.mem_filter.mpr ⟨hi, i.isLt⟩)))
      (fun w hw => by
        by_cases hlt : w < N + N
        · right; left
          refine ⟨w, hlt, ?_⟩
          ext z
          simp only [Su, Finset.mem_filter,
            mem_cone_iff_of_not_gate C (by omega : ¬ (N + N ≤ w ∧ w - (N + N) < C.gates.length)),
            Finset.mem_singleton]
          constructor
          · rintro ⟨rfl, _⟩; rfl
          · rintro rfl; exact ⟨rfl, hlt⟩
        · right; right
          have hwC : w ∈ coneOut := cone_subset_of_mem (N + N) C hrb C.output wStar hwStarC hw
          have hwL : w ∈ L := Finset.mem_filter.mpr ⟨hwC, by omega⟩
          have hwP := hLgates w hwL
          set a := (gateAt C (w - (N + N))).inputs.getD 0 0
          set b := (gateAt C (w - (N + N))).inputs.getD 1 0
          have hlen2 : (gateAt C (w - (N + N))).inputs.length = 2 := by
            apply hAO.2.2; unfold gateAt; rw [List.getD_eq_getElem _ _ hwP.2]; exact List.getElem_mem hwP.2
          have hlist : (gateAt C (w - (N + N))).inputs = [a, b] := by
            rcases hl : (gateAt C (w - (N + N))).inputs with _ | ⟨x, _ | ⟨y, _ | _⟩⟩ <;> simp [hl] at hlen2
            simp [a, b, hl]
          have ha_mem : a ∈ (gateAt C (w - (N + N))).inputs := by rw [hlist]; simp
          have hb_mem : b ∈ (gateAt C (w - (N + N))).inputs := by rw [hlist]; simp
          have ha_lt : a < w := by have := hrb (w - (N + N)) hwP.2 a ha_mem; omega
          have hb_lt : b < w := by have := hrb (w - (N + N)) hwP.2 b hb_mem; omega
          have haA : a ∈ Au := cone_subset_of_mem (N + N) C hrb wStar w hw (mem_cone_of_input (N + N) C hrb hwP.1 hwP.2 ha_mem)
          have hbA : b ∈ Au := cone_subset_of_mem (N + N) C hrb wStar w hw (mem_cone_of_input (N + N) C hrb hwP.1 hwP.2 hb_mem)
          refine ⟨a, haA, b, hbA, ha_lt, hb_lt, ?_, ?_, ?_⟩
          · exact Finset.disjoint_filter_filter (hCone_disj_star w hwL hw)
          · intro z hz
            have hz' := Finset.mem_filter.mp hz
            rw [mem_cone_iff_of_gate C hrb hwP.1 hwP.2] at hz'
            rcases hz'.1 with rfl | ⟨u, hu, hzu⟩
            · omega
            · rw [hlist] at hu; simp at hu
              rcases hu with rfl | rfl
              · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hzu, hz'.2⟩)
              · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hzu, hz'.2⟩)
          · have hweq : w = (N + N) + (w - (N + N)) := by omega
            by_cases hop : (gateAt C (w - (N + N))).op = GateOp.and
            · left; intro x; simp only [Hu]; conv_lhs => rw [hweq, wval_gate C hAO x hwP.2]
              simp [a, b, hop]
            · right; intro x; simp only [Hu]; conv_lhs => rw [hweq, wval_gate C hAO x hwP.2]
              simp [a, b, hop])
      (v1 := Fin.castAdd N p1) (v2 := Fin.natAdd N l1) (v3 := Fin.castAdd N p2) (v4 := Fin.natAdd N l2)
      (fun h => by have := congrArg Fin.val h; simp at this; omega)
      (fun h => hp12 (Fin.ext (by simpa using congrArg Fin.val h)))
      (fun h => by have := congrArg Fin.val h; simp at this; omega)
      (fun h => by have := congrArg Fin.val h; simp at this; omega)
      (fun h => hl12 (Fin.ext (by simpa using congrArg Fin.val h)))
      (fun h => by have := congrArg Fin.val h; simp at this; omega)
      wStar (mem_cone_self (N + N) C wStar)
    apply hno
    dsimp only [Hu]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hwStar_eq _ (h1u _ hp1u)]; exact hf_ind1 _
    · rw [hwStar_eq _ (h1u _ hl1u)]; exact hf_ind1 _
    · rw [hwStar_eq _ (h1u _ hp2u)]; exact hf_ind1 _
    · rw [hwStar_eq _ (h1u _ hl2u)]; exact hf_ind1 _
    · rw [hwStar_eq _ (h2u _ _ hp1u hl1u), hf_ind2_pl]; simp [h11]
    · rw [hwStar_eq _ (h2u _ _ hl1u hp2u)]
      rw [show ind2 (Fin.natAdd N l1) (Fin.castAdd N p2) = ind2 (Fin.castAdd N p2) (Fin.natAdd N l1) from
        by funext i; simp [ind2, or_comm]]
      rw [hf_ind2_pl]; simp [h21]
    · rw [hwStar_eq _ (h2u _ _ hp2u hl2u), hf_ind2_pl]; simp [h22]
    · rw [hwStar_eq _ (h2u _ _ hp1u hl2u), hf_ind2_pl]; simp [hnot12]
  -- 3. Bound crossing edges E_UV and E_VU
  have hCross_UV : ((UP ×ˢ VL).filter (fun pl => I pl.1 pl.2)).card ≤ N := by
    set EUV := (UP ×ˢ VL).filter (fun pl => I pl.1 pl.2)
    set S := UP.filter (fun p => wval C (ind1 (Fin.castAdd N p)) wStar ≠ wval C zeroIn wStar)
    have hEUV_sub : EUV ⊆ S ×ˢ VL := by
      intro ⟨p, l⟩ hpl
      have hm := Finset.mem_filter.mp hpl
      have hpUP := (Finset.mem_product.mp hm.1).1
      have hlVL := (Finset.mem_product.mp hm.1).2
      refine Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨hpUP, ?_⟩, hlVL⟩
      intro heq
      have hws1 : wval C (ind2 (Fin.castAdd N p) (Fin.natAdd N l)) wStar =
          wval C (ind1 (Fin.castAdd N p)) wStar := wval_eq_of_cone C hAO wStar (fun i hi => by
        have hne : i ≠ Fin.natAdd N l := fun h => (Finset.mem_filter.mp hlVL).2 (h ▸ hi)
        simp only [ind2, ind1, hne, or_false])
      have hws2 : wval C (ind1 (Fin.natAdd N l)) wStar = wval C zeroIn wStar :=
        wval_eq_of_cone C hAO wStar (fun i hi => by
          have hne : i ≠ Fin.natAdd N l := fun h => (Finset.mem_filter.mp hlVL).2 (h ▸ hi)
          simp only [ind1, zeroIn, hne, decide_false])
      have hout : wval C (ind2 (Fin.castAdd N p) (Fin.natAdd N l)) C.output =
          wval C (ind1 (Fin.natAdd N l)) C.output := by
        rw [← evalMod_eq_wval C hAO wStar _ C.output, ← evalMod_eq_wval C hAO wStar _ C.output]
        rw [hws1, heq, ← hws2]
        exact hEvalMod_dep _ C.output (mem_cone_self (N + N) C C.output) (Or.inr hOut_not_star) _ _ (fun i hi => by
          have hne : i ≠ Fin.castAdd N p := fun h => (Finset.mem_sdiff.mp hi).2 (h ▸ (Finset.mem_filter.mp hpUP).2)
          simp only [ind2, ind1, hne, false_or])
      rw [hf_ind2_pl, hf_ind1] at hout
      simp [hm.2] at hout
    by_cases hS : S.card ≤ 1
    · calc EUV.card ≤ (S ×ˢ VL).card := Finset.card_le_card hEUV_sub
        _ = S.card * VL.card := Finset.card_product S VL
        _ ≤ 1 * N := Nat.mul_le_mul hS (by
            calc VL.card ≤ (Finset.univ : Finset (Fin N)).card := Finset.card_le_univ _
              _ = N := by simp)
        _ = N := one_mul N
    · have hS2 : 1 < S.card := by omega
      obtain ⟨p1, hp1S⟩ := Finset.card_pos.mp (by omega : 0 < S.card)
      obtain ⟨p2, hp2S, hp2ne⟩ := Finset.exists_mem_ne hS2 p1
      have hSameNb : ∀ p ∈ S, ∀ q' ∈ S, ∀ l ∈ VL, I p l → I q' l := by
        intro p hpS q' hqS l hlVL hIpl
        have hwp : wval C (ind1 (Fin.castAdd N p)) wStar = wval C (ind1 (Fin.castAdd N q')) wStar :=
          bool_eq_of_ne (Finset.mem_filter.mp hpS).2 (Finset.mem_filter.mp hqS).2
        have hws1 : wval C (ind2 (Fin.castAdd N p) (Fin.natAdd N l)) wStar =
            wval C (ind1 (Fin.castAdd N p)) wStar := wval_eq_of_cone C hAO wStar (fun i hi => by
          have hne : i ≠ Fin.natAdd N l := fun h => (Finset.mem_filter.mp hlVL).2 (h ▸ hi)
          simp only [ind2, ind1, hne, or_false])
        have hws2 : wval C (ind2 (Fin.castAdd N q') (Fin.natAdd N l)) wStar =
            wval C (ind1 (Fin.castAdd N q')) wStar := wval_eq_of_cone C hAO wStar (fun i hi => by
          have hne : i ≠ Fin.natAdd N l := fun h => (Finset.mem_filter.mp hlVL).2 (h ▸ hi)
          simp only [ind2, ind1, hne, or_false])
        have hout : wval C (ind2 (Fin.castAdd N p) (Fin.natAdd N l)) C.output =
            wval C (ind2 (Fin.castAdd N q') (Fin.natAdd N l)) C.output := by
          rw [← evalMod_eq_wval C hAO wStar _ C.output, ← evalMod_eq_wval C hAO wStar _ C.output]
          rw [hws1, hws2, hwp]
          exact hEvalMod_dep _ C.output (mem_cone_self (N + N) C C.output) (Or.inr hOut_not_star) _ _ (fun i hi => by
            have hn1 : i ≠ Fin.castAdd N p := fun h =>
              (Finset.mem_sdiff.mp hi).2 (h ▸ (Finset.mem_filter.mp (Finset.mem_filter.mp hpS).1).2)
            have hn2 : i ≠ Fin.castAdd N q' := fun h =>
              (Finset.mem_sdiff.mp hi).2 (h ▸ (Finset.mem_filter.mp (Finset.mem_filter.mp hqS).1).2)
            simp only [ind2, hn1, hn2, false_or])
        rw [hf_ind2_pl, hf_ind2_pl] at hout
        simpa [hIpl] using hout.symm
      have hinj : Set.InjOn Prod.fst (EUV : Set (Fin N × Fin N)) := by
        intro ⟨a1, l1⟩ h1 ⟨a2, l2⟩ h2 hfst
        dsimp only at hfst; subst hfst
        have hm1 := Finset.mem_filter.mp h1
        have hm2 := Finset.mem_filter.mp h2
        have haS : a1 ∈ S := (Finset.mem_product.mp (hEUV_sub h1)).1
        have hl1VL : l1 ∈ VL := (Finset.mem_product.mp hm1.1).2
        have hl2VL : l2 ∈ VL := (Finset.mem_product.mp hm2.1).2
        have h11 : I p1 l1 := hSameNb a1 haS p1 hp1S l1 hl1VL hm1.2
        have h21 : I p2 l1 := hSameNb a1 haS p2 hp2S l1 hl1VL hm1.2
        have h12 : I p1 l2 := hSameNb a1 haS p1 hp1S l2 hl2VL hm2.2
        have h22 : I p2 l2 := hSameNb a1 haS p2 hp2S l2 hl2VL hm2.2
        obtain ⟨l, _, huniq⟩ := hUniq p1 p2 hp2ne.symm
        exact Prod.ext rfl ((huniq l1 ⟨h11, h21⟩).trans (huniq l2 ⟨h12, h22⟩).symm)
      calc EUV.card = (EUV.image Prod.fst).card := (Finset.card_image_of_injOn hinj).symm
        _ ≤ (Finset.univ : Finset (Fin N)).card := Finset.card_le_univ _
        _ = N := by simp
  have hCross_VU : ((VP ×ˢ UL).filter (fun pl => I pl.1 pl.2)).card ≤ N := by
    set EVU := (VP ×ˢ UL).filter (fun pl => I pl.1 pl.2)
    set S := UL.filter (fun l => wval C (ind1 (Fin.natAdd N l)) wStar ≠ wval C zeroIn wStar)
    have hEVU_sub : EVU ⊆ VP ×ˢ S := by
      intro ⟨p, l⟩ hpl
      have hm := Finset.mem_filter.mp hpl
      have hpVP := (Finset.mem_product.mp hm.1).1
      have hlUL := (Finset.mem_product.mp hm.1).2
      refine Finset.mem_product.mpr ⟨hpVP, Finset.mem_filter.mpr ⟨hlUL, ?_⟩⟩
      intro heq
      have hws1 : wval C (ind2 (Fin.castAdd N p) (Fin.natAdd N l)) wStar =
          wval C (ind1 (Fin.natAdd N l)) wStar := wval_eq_of_cone C hAO wStar (fun i hi => by
        have hne : i ≠ Fin.castAdd N p := fun h => (Finset.mem_filter.mp hpVP).2 (h ▸ hi)
        simp only [ind2, ind1, hne, false_or])
      have hws2 : wval C (ind1 (Fin.castAdd N p)) wStar = wval C zeroIn wStar :=
        wval_eq_of_cone C hAO wStar (fun i hi => by
          have hne : i ≠ Fin.castAdd N p := fun h => (Finset.mem_filter.mp hpVP).2 (h ▸ hi)
          simp only [ind1, zeroIn, hne, decide_false])
      have hout : wval C (ind2 (Fin.castAdd N p) (Fin.natAdd N l)) C.output =
          wval C (ind1 (Fin.castAdd N p)) C.output := by
        rw [← evalMod_eq_wval C hAO wStar _ C.output, ← evalMod_eq_wval C hAO wStar _ C.output]
        rw [hws1, heq, ← hws2]
        exact hEvalMod_dep _ C.output (mem_cone_self (N + N) C C.output) (Or.inr hOut_not_star) _ _ (fun i hi => by
          have hne : i ≠ Fin.natAdd N l := fun h => (Finset.mem_sdiff.mp hi).2 (h ▸ (Finset.mem_filter.mp hlUL).2)
          simp only [ind2, ind1, hne, or_false])
      rw [hf_ind2_pl, hf_ind1] at hout
      simp [hm.2] at hout
    by_cases hS : S.card ≤ 1
    · calc EVU.card ≤ (VP ×ˢ S).card := Finset.card_le_card hEVU_sub
        _ = VP.card * S.card := Finset.card_product VP S
        _ ≤ N * 1 := Nat.mul_le_mul (by
            calc VP.card ≤ (Finset.univ : Finset (Fin N)).card := Finset.card_le_univ _
              _ = N := by simp) hS
        _ = N := mul_one N
    · have hS2 : 1 < S.card := by omega
      obtain ⟨l1, hl1S⟩ := Finset.card_pos.mp (by omega : 0 < S.card)
      obtain ⟨l2, hl2S, hl2ne⟩ := Finset.exists_mem_ne hS2 l1
      have hSameNb : ∀ l ∈ S, ∀ l' ∈ S, ∀ p ∈ VP, I p l → I p l' := by
        intro l hlS l' hl'S p hpVP hIpl
        have hwl : wval C (ind1 (Fin.natAdd N l)) wStar = wval C (ind1 (Fin.natAdd N l')) wStar :=
          bool_eq_of_ne (Finset.mem_filter.mp hlS).2 (Finset.mem_filter.mp hl'S).2
        have hws1 : wval C (ind2 (Fin.castAdd N p) (Fin.natAdd N l)) wStar =
            wval C (ind1 (Fin.natAdd N l)) wStar := wval_eq_of_cone C hAO wStar (fun i hi => by
          have hne : i ≠ Fin.castAdd N p := fun h => (Finset.mem_filter.mp hpVP).2 (h ▸ hi)
          simp only [ind2, ind1, hne, false_or])
        have hws2 : wval C (ind2 (Fin.castAdd N p) (Fin.natAdd N l')) wStar =
            wval C (ind1 (Fin.natAdd N l')) wStar := wval_eq_of_cone C hAO wStar (fun i hi => by
          have hne : i ≠ Fin.castAdd N p := fun h => (Finset.mem_filter.mp hpVP).2 (h ▸ hi)
          simp only [ind2, ind1, hne, false_or])
        have hout : wval C (ind2 (Fin.castAdd N p) (Fin.natAdd N l)) C.output =
            wval C (ind2 (Fin.castAdd N p) (Fin.natAdd N l')) C.output := by
          rw [← evalMod_eq_wval C hAO wStar _ C.output, ← evalMod_eq_wval C hAO wStar _ C.output]
          rw [hws1, hws2, hwl]
          exact hEvalMod_dep _ C.output (mem_cone_self (N + N) C C.output) (Or.inr hOut_not_star) _ _ (fun i hi => by
            have hn1 : i ≠ Fin.natAdd N l := fun h =>
              (Finset.mem_sdiff.mp hi).2 (h ▸ (Finset.mem_filter.mp (Finset.mem_filter.mp hlS).1).2)
            have hn2 : i ≠ Fin.natAdd N l' := fun h =>
              (Finset.mem_sdiff.mp hi).2 (h ▸ (Finset.mem_filter.mp (Finset.mem_filter.mp hl'S).1).2)
            simp only [ind2, hn1, hn2, or_false])
        rw [hf_ind2_pl, hf_ind2_pl] at hout
        simpa [hIpl] using hout.symm
      have hinj : Set.InjOn Prod.snd (EVU : Set (Fin N × Fin N)) := by
        intro ⟨p1, b1⟩ h1 ⟨p2, b2⟩ h2 hsnd
        dsimp only at hsnd; subst hsnd
        have hm1 := Finset.mem_filter.mp h1
        have hm2 := Finset.mem_filter.mp h2
        have hbS : b1 ∈ S := (Finset.mem_product.mp (hEVU_sub h1)).2
        have hp1VP : p1 ∈ VP := (Finset.mem_product.mp hm1.1).1
        have hp2VP : p2 ∈ VP := (Finset.mem_product.mp hm2.1).1
        have h11 : I p1 l1 := hSameNb b1 hbS l1 hl1S p1 hp1VP hm1.2
        have h12 : I p1 l2 := hSameNb b1 hbS l2 hl2S p1 hp1VP hm1.2
        have h21 : I p2 l1 := hSameNb b1 hbS l1 hl1S p2 hp2VP hm2.2
        have h22 : I p2 l2 := hSameNb b1 hbS l2 hl2S p2 hp2VP hm2.2
        by_contra hne
        have hpne : p1 ≠ p2 := fun h => hne (Prod.ext h rfl)
        obtain ⟨l, _, huniq⟩ := hUniq p1 p2 hpne
        exact hl2ne.symm ((huniq l1 ⟨h11, h21⟩).trans (huniq l2 ⟨h12, h22⟩).symm)
      calc EVU.card = (EVU.image Prod.snd).card := (Finset.card_image_of_injOn hinj).symm
        _ ≤ (Finset.univ : Finset (Fin N)).card := Finset.card_le_univ _
        _ = N := by simp
  -- 4. Total edge count contradiction!
  set Eall := (Finset.univ : Finset (Fin N × Fin N)).filter (fun pl => I pl.1 pl.2)
  have hEall_card : Eall.card = N * (q + 1) := by
    have h1 : Eall.card = ∑ l : Fin N, (Finset.univ.filter (fun p : Fin N => I p l)).card := by
      have hbi : Eall = Finset.univ.biUnion (fun l : Fin N =>
          (Finset.univ.filter (fun p : Fin N => I p l)).image (fun p => (p, l))) := by
        ext ⟨p, l⟩
        simp only [Eall, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion,
          Finset.mem_image, Prod.mk.injEq]
        constructor
        · intro h; exact ⟨l, p, h, rfl, rfl⟩
        · rintro ⟨l', p', h, rfl, rfl⟩; exact h
      rw [hbi, Finset.card_biUnion]
      · apply Finset.sum_congr rfl
        intro l _
        exact Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.injEq ..).mp h |>.1)
      · intro l1 _ l2 _ hne
        show Disjoint _ _
        rw [Finset.disjoint_left]
        intro ⟨p, l⟩ h1 h2
        obtain ⟨_, _, heq1⟩ := Finset.mem_image.mp h1
        obtain ⟨_, _, heq2⟩ := Finset.mem_image.mp h2
        have hl1 : l1 = l := ((Prod.mk.injEq ..).mp heq1).2
        have hl2 : l2 = l := ((Prod.mk.injEq ..).mp heq2).2
        exact hne (hl1.trans hl2.symm)
    rw [h1]
    have h2 : ∀ l : Fin N, (Finset.univ.filter (fun p : Fin N => I p l)).card = q + 1 := by
      intro l
      rw [← Fintype.card_subtype]
      exact hCard l
    simp [h2]
  have hEall_sub : Eall ⊆
      ((UP ×ˢ UL).filter (fun pl => I pl.1 pl.2)) ∪
      ((VP ×ˢ VL).filter (fun pl => I pl.1 pl.2)) ∪
      ((UP ×ˢ VL).filter (fun pl => I pl.1 pl.2)) ∪
      ((VP ×ˢ UL).filter (fun pl => I pl.1 pl.2)) := by
    intro ⟨p, l⟩ hpl
    have hI := (Finset.mem_filter.mp hpl).2
    by_cases hp : (Fin.castAdd N p).val ∈ cone (N + N) C wStar <;>
      by_cases hl : (Fin.natAdd N l).val ∈ cone (N + N) C wStar
    · simp only [UP, UL, Finset.mem_union, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and]
      exact Or.inl (Or.inl (Or.inl ⟨⟨hp, hl⟩, hI⟩))
    · simp only [UP, VL, Finset.mem_union, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and]
      exact Or.inl (Or.inr ⟨⟨hp, hl⟩, hI⟩)
    · simp only [VP, UL, Finset.mem_union, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and]
      exact Or.inr ⟨⟨hp, hl⟩, hI⟩
    · simp only [VP, VL, Finset.mem_union, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and]
      exact Or.inl (Or.inl (Or.inr ⟨⟨hp, hl⟩, hI⟩))
  have hE_UU := card_edges_of_no_P4 I UP UL hNoP4_U
  have hE_VV := card_edges_of_no_P4 I VP VL hNoP4_V
  have hP_sum : UP.card + VP.card = N := by
    have hD : Disjoint UP VP := by
      rw [Finset.disjoint_left]
      intro p h1 h2
      exact (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2
    have hU : UP ∪ VP = Finset.univ := by
      ext p
      simp only [UP, VP, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      exact em _
    rw [← Finset.card_union_of_disjoint hD, hU, Finset.card_univ, Fintype.card_fin]
  have hL_sum : UL.card + VL.card = N := by
    have hD : Disjoint UL VL := by
      rw [Finset.disjoint_left]
      intro l h1 h2
      exact (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2
    have hU : UL ∪ VL = Finset.univ := by
      ext l
      simp only [UL, VL, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      exact em _
    rw [← Finset.card_union_of_disjoint hD, hU, Finset.card_univ, Fintype.card_fin]
  have hTot : Eall.card ≤ (UP.card + UL.card) + (VP.card + VL.card) + N + N := by
    calc Eall.card
        ≤ (((UP ×ˢ UL).filter (fun pl => I pl.1 pl.2)) ∪
           ((VP ×ˢ VL).filter (fun pl => I pl.1 pl.2)) ∪
           ((UP ×ˢ VL).filter (fun pl => I pl.1 pl.2)) ∪
           ((VP ×ˢ UL).filter (fun pl => I pl.1 pl.2))).card := Finset.card_le_card hEall_sub
      _ ≤ (((UP ×ˢ UL).filter (fun pl => I pl.1 pl.2)) ∪
           ((VP ×ˢ VL).filter (fun pl => I pl.1 pl.2)) ∪
           ((UP ×ˢ VL).filter (fun pl => I pl.1 pl.2))).card +
           ((VP ×ˢ UL).filter (fun pl => I pl.1 pl.2)).card := Finset.card_union_le _ _
      _ ≤ (((UP ×ˢ UL).filter (fun pl => I pl.1 pl.2)) ∪
           ((VP ×ˢ VL).filter (fun pl => I pl.1 pl.2))).card +
           ((UP ×ˢ VL).filter (fun pl => I pl.1 pl.2)).card +
           ((VP ×ˢ UL).filter (fun pl => I pl.1 pl.2)).card := by
            have := Finset.card_union_le (((UP ×ˢ UL).filter (fun pl => I pl.1 pl.2)) ∪
              ((VP ×ˢ VL).filter (fun pl => I pl.1 pl.2))) ((UP ×ˢ VL).filter (fun pl => I pl.1 pl.2))
            omega
      _ ≤ ((UP ×ˢ UL).filter (fun pl => I pl.1 pl.2)).card +
           ((VP ×ˢ VL).filter (fun pl => I pl.1 pl.2)).card +
           ((UP ×ˢ VL).filter (fun pl => I pl.1 pl.2)).card +
           ((VP ×ˢ UL).filter (fun pl => I pl.1 pl.2)).card := by
            have := Finset.card_union_le ((UP ×ˢ UL).filter (fun pl => I pl.1 pl.2))
              ((VP ×ˢ VL).filter (fun pl => I pl.1 pl.2))
            omega
      _ ≤ (UP.card + UL.card) + (VP.card + VL.card) + N + N := by omega
  rw [hEall_card] at hTot
  nlinarith

theorem main : ¬ (∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3], (201 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x7 : Fin x2), Fintype.card { x8 : Fin x2 // x3 x8 x7 } = x1 + (1 : ℕ)) → (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x3 x8 x11 ∧ x3 x9 x11) → ∃ (x9 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (x2 + x2) x9 ∧ (∀ (x10 : Fin (x2 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x2 + x2) x9 x10 = Decidable.decide (∃ (x11 : Fin x2) (x12 : Fin x2), x3 x11 x12 ∧ x10 (Fin.castAdd x2 x11) = Bool.true ∧ x10 (Fin.natAdd x2 x12) = Bool.true)) ∧ PEqualNP.ReadK.IsReadK (x2 + x2) x9 (2 : ℕ) ∧ x9.size ≤ (2 : ℕ) * x2) := by
  intro hall
  let e : Pt ≃ Fin N0 := Fintype.equivFinOfCardEq card_Pt
  let I : Fin N0 → Fin N0 → Prop := fun p l => incPt (e.symm p) (e.symm l)
  haveI : DecidableRel I := fun p l => inferInstanceAs (Decidable (incPt (e.symm p) (e.symm l)))
  have hCard : ∀ l : Fin N0, Fintype.card { p : Fin N0 // I p l } = q0 + 1 := by
    intro l
    rw [← card_line_Pt (e.symm l)]
    exact Fintype.card_congr
      { toFun := fun ⟨p, hp⟩ => ⟨e.symm p, hp⟩
        invFun := fun ⟨u, hu⟩ => ⟨e u, by simpa [I] using hu⟩
        left_inv := fun ⟨p, _⟩ => by simp
        right_inv := fun ⟨u, _⟩ => by simp }
  have hUniq : ∀ p1 p2 : Fin N0, p1 ≠ p2 → ∃! l : Fin N0, I p1 l ∧ I p2 l := by
    intro p1 p2 hne
    have hne' : e.symm p1 ≠ e.symm p2 := fun h => hne (e.symm.injective h)
    obtain ⟨l, ⟨h1, h2⟩, huniq⟩ := unique_line_Pt (e.symm p1) (e.symm p2) hne'
    refine ⟨e l, ⟨by simpa [I] using h1, by simpa [I] using h2⟩, ?_⟩
    intro l' ⟨h1', h2'⟩
    have := huniq (e.symm l') ⟨h1', h2'⟩
    exact e.symm_apply_eq.mp this
  obtain ⟨C, hAO, hEval, _, hSize⟩ := hall q0 N0 I (by decide) rfl hCard hUniq
  exact no_small_circuit I (by decide) rfl hCard hUniq C hAO hEval hSize

end PEqualNP.Outside.L_meta_2461_aux

theorem PEqualNP.Outside.L_meta_2461 : ¬ (∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3], (201 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x7 : Fin x2), Fintype.card { x8 : Fin x2 // x3 x8 x7 } = x1 + (1 : ℕ)) → (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x3 x8 x11 ∧ x3 x9 x11) → ∃ (x9 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (x2 + x2) x9 ∧ (∀ (x10 : Fin (x2 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x2 + x2) x9 x10 = Decidable.decide (∃ (x11 : Fin x2) (x12 : Fin x2), x3 x11 x12 ∧ x10 (Fin.castAdd x2 x11) = Bool.true ∧ x10 (Fin.natAdd x2 x12) = Bool.true)) ∧ PEqualNP.ReadK.IsReadK (x2 + x2) x9 (2 : ℕ) ∧ x9.size ≤ (2 : ℕ) * x2) :=
  PEqualNP.Outside.L_meta_2461_aux.main
