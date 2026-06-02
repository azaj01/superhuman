import Mathlib

set_option autoImplicit false

variable (h : ℕ) (hh : 5 ≤ h)

abbrev Fiber2 (h : ℕ) := Fin (2 * h) × Fin (2 * h)

-- 1. Base Coordinate Definitions
def one2 : Fin (2 * h) := ⟨1, by omega⟩
def mMinusOne2 : Fin (2 * h) := ⟨2 * h - 1, by omega⟩
def mMinusTwo2 : Fin (2 * h) := ⟨2 * h - 2, by omega⟩

def succ2c (x : Fin (2 * h)) : Fin (2 * h) := x + one2 h hh
def pred2c (x : Fin (2 * h)) : Fin (2 * h) := x - one2 h hh

-- 2. Exceptional Set Logic (Defects)
def y2SwitchRow (x : Fin (2 * h)) : Prop :=
  x.val = h + 1 ∨ x.val = h + 2 ∨ x.val = h + 3

instance (x : Fin (2 * h)) : Decidable (y2SwitchRow h x) := by
  unfold y2SwitchRow
  infer_instance

def y2star (x : Fin (2 * h)) : Fin (2 * h) :=
  if y2SwitchRow h x then
    if h % 2 = 0 then mMinusTwo2 h hh else mMinusOne2 h hh
  else
    ⟨2 * h - 1 - x.val, by omega⟩

def A2 (x : Fin (2 * h)) : Fin (2 * h) :=
  succ2c h hh (y2star h hh x)

def activeB2 (x y : Fin (2 * h)) : Prop :=
  if h % 2 = 0 then
    (x.val = h + 1 ∧ y.val ≤ h - 1) ∨
      (x.val = h + 4 ∧ h - 3 ≤ y.val ∧ y.val ≤ 2 * h - 2)
  else
    (x.val = h + 1 ∧ 1 ≤ y.val ∧ y.val ≤ h - 1) ∨
      (x.val = h + 4 ∧ h - 3 ≤ y.val)

instance (x y : Fin (2 * h)) : Decidable (activeB2 h x y) := by
  unfold activeB2
  infer_instance

-- 3. The Round Map
def r2Map (p : Fiber2 h) : Fiber2 h :=
  let x := p.1
  let u := pred2c h hh p.2
  if u = A2 h hh x then
    (succ2c h hh x,
      if x.val = h + 1 ∨ x.val = h + 2 then u else pred2c h hh u)
  else if activeB2 h x u then
    (x, pred2c h hh u)
  else
    (x, u)

-- 4. The Self-Contained Goal
/-- The unrolled Hamiltonicity goal for the Color 2 round map. -/
theorem color2_singleCycle_unrolled (h6 : 6 ≤ h) :
    (∀ p : Fin (2 * h) × Fin (2 * h), (r2Map h hh)^[(2 * h) * (2 * h)] p = p) ∧
    (∀ (p : Fin (2 * h) × Fin (2 * h)) (k : ℕ), 0 < k → k < (2 * h) * (2 * h) → (r2Map h hh)^[k] p ≠ p) := by
  sorry
