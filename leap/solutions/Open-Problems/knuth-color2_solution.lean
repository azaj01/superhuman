import Mathlib
set_option autoImplicit false
set_option linter.unusedTactic false
variable (h : ℕ) (hh : 5 ≤ h)
abbrev Fiber2 (h : ℕ) := Fin (2 * h) × Fin (2 * h)
def one2 : Fin (2 * h) := ⟨1, by omega⟩
def mMinusOne2 : Fin (2 * h) := ⟨2 * h - 1, by omega⟩
def mMinusTwo2 : Fin (2 * h) := ⟨2 * h - 2, by omega⟩
def succ2c (x : Fin (2 * h)) : Fin (2 * h) := x + one2 h hh
def pred2c (x : Fin (2 * h)) : Fin (2 * h) := x - one2 h hh
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

def zero2 : Fin (2 * h) := ⟨0, by omega⟩

def jump_y (x : Fin (2 * h)) : Fin (2 * h) :=
  succ2c h hh (A2 h hh x)

def T_val (x : Fin (2 * h)) : Fin (2 * h) :=
  if x.val = h + 1 ∨ x.val = h + 2 then A2 h hh x else pred2c h hh (A2 h hh x)

def H_val (x : Fin (2 * h)) : Fin (2 * h) :=
  T_val h hh (pred2c h hh x)

def row_map (x : Fin (2 * h)) (y : Fin (2 * h)) : Fin (2 * h) :=
  if y = jump_y h hh x then H_val h hh x
  else if activeB2 h x (pred2c h hh y) then pred2c h hh (pred2c h hh y)
  else pred2c h hh y

def natToFin (c : ℕ) : Fin (2 * h) :=
  ⟨c % (2 * h), by apply Nat.mod_lt; omega⟩

def step_desc (h : ℕ) (hh : 5 ≤ h) (x y : Fin (2 * h)) : ℕ :=
  if activeB2 h x (pred2c h hh y) then 2 else 1

def total_desc (h : ℕ) (hh : 5 ≤ h) (x : Fin (2 * h)) (k : ℕ) : ℕ :=
  match k with
  | 0 => 0
  | n + 1 => total_desc h hh x n + step_desc h hh x ((row_map h hh x)^[n] (H_val h hh x))

def H_sub_J (h : ℕ) (hh : 5 ≤ h) (x : Fin (2 * h)) : ℤ :=
  ((H_val h hh x).val : ℤ) - ((jump_y h hh x).val : ℤ)

def a_act (x : Fin (2 * h)) : Fin (2 * h) :=
  have _hh := hh
  if x.val = h + 1 then
    if h % 2 = 0 then ⟨0, by omega⟩ else ⟨1, by omega⟩
  else
    ⟨h - 3, by omega⟩

def b_act (x : Fin (2 * h)) : Fin (2 * h) :=
  have _hh := hh
  if x.val = h + 1 then
    ⟨h - 1, by omega⟩
  else
    if h % 2 = 0 then ⟨2 * h - 2, by omega⟩ else ⟨2 * h - 1, by omega⟩

def L_act (x : Fin (2 * h)) : ℕ :=
  have _hh := hh
  if x.val = h + 1 then
    if h % 2 = 0 then h - 1 else h - 2
  else
    if h % 2 = 0 then h + 1 else h + 2

def k_track1 (x : Fin (2 * h)) : ℕ :=
  (L_act h hh x - 1) / 2

def k_trans_out (x : Fin (2 * h)) : ℕ :=
  have _hh := hh
  1

def k_out (x : Fin (2 * h)) : ℕ :=
  2 * h - L_act h hh x - 2

def k_trans_in (x : Fin (2 * h)) : ℕ :=
  have _hh := hh
  1

def k_track2 (x : Fin (2 * h)) : ℕ :=
  (L_act h hh x - 1) / 2

def state_y1 (x : Fin (2 * h)) : Fin (2 * h) :=
  succ2c h hh (a_act h hh x)

def state_y2 (x : Fin (2 * h)) : Fin (2 * h) :=
  pred2c h hh (a_act h hh x)

def state_y3 (x : Fin (2 * h)) : Fin (2 * h) :=
  succ2c h hh (b_act h hh x)

def state_y4 (x : Fin (2 * h)) : Fin (2 * h) :=
  pred2c h hh (b_act h hh x)

def is_active_step (h : ℕ) (hh : 5 ≤ h) (x : Fin (2 * h)) (y : Fin (2 * h)) : ℕ :=
  if activeB2 h x (pred2c h hh y) then 1 else 0

def N_active (h : ℕ) (hh : 5 ≤ h) (x : Fin (2 * h)) (k : ℕ) : ℕ :=
  match k with
  | 0 => 0
  | n + 1 => N_active h hh x n + is_active_step h hh x ((row_map h hh x)^[n] (H_val h hh x))

def track1_state (x : Fin (2 * h)) (k : ℕ) : Fin (2 * h) :=
  ⟨((b_act h hh x).val + 2 * h - (2 * k) % (2 * h)) % (2 * h), by
    have : 0 < 2 * h := by omega
    exact Nat.mod_lt _ this⟩

def track2_seq (x : Fin (2 * h)) (i : ℕ) : Fin (2 * h) :=
  match i with
  | 0 => state_y4 h hh x
  | n + 1 => pred2c h hh (pred2c h hh (track2_seq x n))

theorem card_fiber2 (h : ℕ) : Fintype.card (Fin (2 * h) × Fin (2 * h)) = (2 * h) * (2 * h) :=
by
  simp

theorem r2Map_unroll_last (x : Fin (2 * h)) :
  (r2Map h hh)^[2 * h] (x, H_val h hh x) = r2Map h hh ((r2Map h hh)^[2 * h - 1] (x, H_val h hh x)) :=
by
  have h_eq : 2 * h = (2 * h - 1).succ := by omega
  have h_eq2 : (r2Map h hh)^[2 * h] = (r2Map h hh)^[(2 * h - 1).succ] := congrArg (fun n => (r2Map h hh)^[n]) h_eq
  rw [h_eq2]
  exact Function.iterate_succ_apply' (r2Map h hh) (2 * h - 1) (x, H_val h hh x)

theorem r2Map_eq (p : Fin (2 * h) × Fin (2 * h)) :
  r2Map h hh p =
    if p.2 = jump_y h hh p.1 then
      (succ2c h hh p.1, H_val h hh (succ2c h hh p.1))
    else
      (p.1, row_map h hh p.1 p.2) :=
by
  haveI : NeZero (2 * h) := ⟨by omega⟩
  have h_equiv : pred2c h hh p.2 = A2 h hh p.1 ↔ p.2 = jump_y h hh p.1 := by
    unfold jump_y succ2c pred2c
    exact sub_eq_iff_eq_add
  have h_pred_succ : pred2c h hh (succ2c h hh p.1) = p.1 := by
    unfold pred2c succ2c
    exact add_sub_cancel_right p.1 (one2 h hh)
  by_cases h_jump : p.2 = jump_y h hh p.1
  · have h_pred : pred2c h hh p.2 = A2 h hh p.1 := h_equiv.mpr h_jump
    rw [if_pos h_jump]
    unfold r2Map
    dsimp only
    rw [if_pos h_pred]
    ext
    · rfl
    · unfold H_val
      dsimp only
      rw [h_pred_succ]
      unfold T_val
      simp only [h_pred]
  · have h_pred : ¬ (pred2c h hh p.2 = A2 h hh p.1) := mt h_equiv.mp h_jump
    rw [if_neg h_jump]
    unfold r2Map row_map
    dsimp only
    rw [if_neg h_pred]
    rw [if_neg h_jump]
    split_ifs with h_act
    · rfl
    · rfl

theorem H_val_sub_not_jump (x : Fin (2 * h)) (h_gen : ∀ y, ¬ activeB2 h x y) (k : ℕ) (hk : k < 2 * h - 1) :
  H_val h hh x - natToFin h hh k ≠ jump_y h hh x :=
by
  intro contra

  have if_val {P : Prop} [Decidable P] (a b : Fin (2 * h)) :
    (if P then a else b).val = if P then a.val else b.val := by
    split_ifs <;> rfl

  have h_pred (w : Fin (2 * h)) : (pred2c h hh w).val = if w.val = 0 then 2 * h - 1 else w.val - 1 := by
    unfold pred2c one2
    rw [Fin.val_sub]
    have : (⟨1, by omega⟩ : Fin (2 * h)).val = 1 := rfl
    rw [this]
    split_ifs with hw0
    · rw [hw0]
      have eq1 : 2 * h - 1 + 0 = 2 * h - 1 := by omega
      have eq1' : 0 + (2 * h - 1) = 2 * h - 1 := by omega
      try rw [eq1]
      try rw [eq1']
      apply Nat.mod_eq_of_lt; omega
    · have eq2 : 2 * h - 1 + w.val = w.val - 1 + 2 * h := by omega
      have eq3 : w.val + (2 * h - 1) = w.val - 1 + 2 * h := by omega
      try rw [eq2]
      try rw [eq3]
      rw [Nat.add_mod_right]
      apply Nat.mod_eq_of_lt; omega

  have h_succ (w : Fin (2 * h)) : (succ2c h hh w).val = if w.val = 2 * h - 1 then 0 else w.val + 1 := by
    unfold succ2c one2
    rw [Fin.val_add]
    have : (⟨1, by omega⟩ : Fin (2 * h)).val = 1 := rfl
    rw [this]
    split_ifs with h_max
    · rw [h_max]; have : 2 * h - 1 + 1 = 2 * h := by omega
      rw [this, Nat.mod_self]
    · apply Nat.mod_eq_of_lt; omega

  have h_y2_val (w : Fin (2 * h)) : (y2star h hh w).val =
    if w.val = h + 1 ∨ w.val = h + 2 ∨ w.val = h + 3 then
      if h % 2 = 0 then 2 * h - 2 else 2 * h - 1
    else 2 * h - 1 - w.val := by
    unfold y2star y2SwitchRow mMinusTwo2 mMinusOne2
    rw [if_val]
    split_ifs <;> rfl

  have h_A2_val (w : Fin (2 * h)) : (A2 h hh w).val =
    if w.val = h + 1 ∨ w.val = h + 2 ∨ w.val = h + 3 then
      if h % 2 = 0 then 2 * h - 1 else 0
    else if w.val = 0 then 0 else 2 * h - w.val := by
    unfold A2
    have hs := h_succ (y2star h hh w)
    have hy := h_y2_val w
    rw [hy] at hs
    rw [hs]
    have hw_lt : w.val < 2 * h := w.isLt
    have h_h_ge : 5 ≤ h := hh
    split_ifs <;> omega

  have h_H_eq_A2 : H_val h hh x = A2 h hh x := by
    apply Fin.ext
    unfold H_val T_val
    rw [if_val]
    have v_px := h_pred x
    have v_a2_px := h_A2_val (pred2c h hh x)
    have v_a2_x := h_A2_val x
    have v_pred_a2_px := h_pred (A2 h hh (pred2c h hh x))
    rw [v_px] at v_a2_px
    rw [v_a2_px] at v_pred_a2_px
    rw [v_px, v_a2_px, v_pred_a2_px, v_a2_x]

    have h_xv : x.val < 2 * h := x.isLt
    have h_h_ge : 5 ≤ h := hh

    have hx1 : x.val ≠ h + 1 := by
      intro hx
      have hy : activeB2 h x ⟨1, by omega⟩ := by
        unfold activeB2
        have yval : (⟨1, by omega⟩ : Fin (2 * h)).val = 1 := rfl
        rw [yval]
        split_ifs with h_even
        · left; exact ⟨hx, by omega⟩
        · left; exact ⟨hx, by omega, by omega⟩
      exact h_gen ⟨1, by omega⟩ hy

    have hx4 : x.val ≠ h + 4 := by
      intro hx
      have hy : activeB2 h x ⟨h - 3, by omega⟩ := by
        unfold activeB2
        have yval : (⟨h - 3, by omega⟩ : Fin (2 * h)).val = h - 3 := rfl
        rw [yval]
        split_ifs with h_even
        · right; exact ⟨hx, by omega, by omega⟩
        · right; exact ⟨hx, by omega⟩
      exact h_gen ⟨h - 3, by omega⟩ hy

    split_ifs <;> omega

  haveI : NeZero (2 * h) := ⟨by omega⟩

  have h_eq : A2 h hh x + (- natToFin h hh k) = A2 h hh x + one2 h hh := by
    calc A2 h hh x + (- natToFin h hh k)
      _ = A2 h hh x - natToFin h hh k := (sub_eq_add_neg _ _).symm
      _ = H_val h hh x - natToFin h hh k := by rw [h_H_eq_A2]
      _ = jump_y h hh x := contra
      _ = A2 h hh x + one2 h hh := rfl

  have h_cancel : - natToFin h hh k = one2 h hh := by
    calc - natToFin h hh k
      _ = 0 + (- natToFin h hh k) := by rw [zero_add]
      _ = (- A2 h hh x + A2 h hh x) + (- natToFin h hh k) := by rw [← neg_add_cancel (A2 h hh x)]
      _ = - A2 h hh x + (A2 h hh x + (- natToFin h hh k)) := by rw [add_assoc]
      _ = - A2 h hh x + (A2 h hh x + one2 h hh) := by rw [h_eq]
      _ = (- A2 h hh x + A2 h hh x) + one2 h hh := by rw [← add_assoc]
      _ = 0 + one2 h hh := by rw [neg_add_cancel]
      _ = one2 h hh := by rw [zero_add]

  have h_sum_zero : one2 h hh + natToFin h hh k = 0 := by
    calc one2 h hh + natToFin h hh k
      _ = - natToFin h hh k + natToFin h hh k := by rw [← h_cancel]
      _ = 0 := by rw [neg_add_cancel]

  have h_sum_val : (one2 h hh + natToFin h hh k).val = 0 := by
    rw [h_sum_zero]
    rfl

  have hk_mod : (natToFin h hh k).val = k := by
    unfold natToFin
    exact Nat.mod_eq_of_lt (by omega)

  have h_sum_val_mod : (one2 h hh + natToFin h hh k).val = (1 + k) % (2 * h) := by
    rw [Fin.val_add]
    have h1 : (one2 h hh).val = 1 := rfl
    rw [h1, hk_mod]

  have h_mod_eq : (1 + k) % (2 * h) = 0 := by
    rw [← h_sum_val_mod, h_sum_val]

  have h_mod_eq2 : (1 + k) % (2 * h) = 1 + k := by
    apply Nat.mod_eq_of_lt
    omega

  rw [h_mod_eq2] at h_mod_eq
  omega

theorem row_map_generic_iter (x : Fin (2 * h)) (h_gen : ∀ y, ¬ activeB2 h x y) (k : ℕ) (hk : k ≤ 2 * h - 1) :
  (row_map h hh x)^[k] (H_val h hh x) = H_val h hh x - natToFin h hh k :=
by
  have _inst : NeZero (2 * h) := ⟨by omega⟩
  induction k with
  | zero =>
    have h_eq : H_val h hh x = H_val h hh x - natToFin h hh 0 := by
      have h_zero : natToFin h hh 0 = 0 := by ext; rfl
      rw [h_zero, sub_zero]
    exact h_eq
  | succ k ih =>
    have hk_lt : k + 1 < 2 * h := by omega
    have hk_le : k ≤ 2 * h - 1 := by omega
    rw [Function.iterate_succ_apply']
    rw [ih hk_le]
    unfold row_map

    have h1 : x.val ≠ h + 1 := by
      intro hx
      have h_act := h_gen ⟨1, by omega⟩
      unfold activeB2 at h_act
      split_ifs at h_act
      · apply h_act; left; exact ⟨hx, by change 1 ≤ h - 1; omega⟩
      · apply h_act; left; exact ⟨hx, by change 1 ≤ 1 ∧ 1 ≤ h - 1; exact ⟨by omega, by omega⟩⟩
    have h4 : x.val ≠ h + 4 := by
      intro hx
      have h_act := h_gen ⟨h - 3, by omega⟩
      unfold activeB2 at h_act
      split_ifs at h_act
      · apply h_act; right; exact ⟨hx, by change h - 3 ≤ h - 3 ∧ h - 3 ≤ 2 * h - 2; exact ⟨by omega, by omega⟩⟩
      · apply h_act; right; exact ⟨hx, by change h - 3 ≤ h - 3; omega⟩

    have hj_fin : jump_y h hh x = H_val h hh x + one2 h hh := by
      ext
      have h_sz : ∀ z : Fin (2 * h), (succ2c h hh z).val = if z.val = 2 * h - 1 then 0 else z.val + 1 := by
        intro z; have eq : (succ2c h hh z).val = (z.val + 1) % (2 * h) := rfl
        rw [eq]; split_ifs with h0
        · rw [h0]; have h2 : 2 * h - 1 + 1 = 2 * h := by omega
          rw [h2]; exact Nat.mod_self (2 * h)
        · have h_lt : z.val + 1 < 2 * h := by have := z.isLt; omega
          exact Nat.mod_eq_of_lt h_lt

      have h_pz : ∀ z : Fin (2 * h), (pred2c h hh z).val = if z.val = 0 then 2 * h - 1 else z.val - 1 := by
        intro z; have eq : (pred2c h hh z).val = (2 * h - 1 + z.val) % (2 * h) := by
          unfold pred2c one2; exact congrArg Fin.val (Fin.sub_def z ⟨1, by omega⟩)
        rw [eq]; split_ifs with h0
        · rw [h0, add_zero]; exact Nat.mod_eq_of_lt (by omega)
        · have h_eq : 2 * h - 1 + z.val = 2 * h + (z.val - 1) := by have := z.isLt; omega
          rw [h_eq, Nat.add_mod, Nat.mod_self, zero_add, Nat.mod_mod]
          exact Nat.mod_eq_of_lt (by have := z.isLt; omega)

      have h_y2_val : ∀ z : Fin (2 * h), (y2star h hh z).val = if z.val = h + 1 ∨ z.val = h + 2 ∨ z.val = h + 3 then (if h % 2 = 0 then 2 * h - 2 else 2 * h - 1) else 2 * h - 1 - z.val := by
        intro z; unfold y2star y2SwitchRow mMinusTwo2 mMinusOne2; split_ifs <;> rfl

      have h_A2_val : ∀ z : Fin (2 * h), (A2 h hh z).val = if (y2star h hh z).val = 2 * h - 1 then 0 else (y2star h hh z).val + 1 := by
        intro z; exact h_sz (y2star h hh z)

      have h_jump_val : (jump_y h hh x).val = if (A2 h hh x).val = 2 * h - 1 then 0 else (A2 h hh x).val + 1 := by
        exact h_sz (A2 h hh x)

      have h_H_val : (H_val h hh x).val = if (pred2c h hh x).val = h + 1 ∨ (pred2c h hh x).val = h + 2 then (A2 h hh (pred2c h hh x)).val else (pred2c h hh (A2 h hh (pred2c h hh x))).val := by
        unfold H_val T_val; split_ifs <;> rfl

      change (jump_y h hh x).val = (succ2c h hh (H_val h hh x)).val
      rw [h_sz, h_jump_val, h_H_val]
      clear h_sz h_jump_val h_H_val

      obtain hx0 | hx1 | hx2 | hx3 | h_other : x.val = 0 ∨ x.val = 1 ∨ x.val = h + 2 ∨ x.val = h + 3 ∨ (x.val ≠ 0 ∧ x.val ≠ 1 ∧ x.val ≠ h + 2 ∧ x.val ≠ h + 3) := by omega
      · have h_px : (pred2c h hh x).val = 2 * h - 1 := by
          rw [h_pz]
          have hc : x.val = 0 := hx0
          rw [if_pos hc]
        have h_y2_px : (y2star h hh (pred2c h hh x)).val = 0 := by
          rw [h_y2_val]
          have hc : ¬((pred2c h hh x).val = h + 1 ∨ (pred2c h hh x).val = h + 2 ∨ (pred2c h hh x).val = h + 3) := by rw [h_px]; omega
          rw [if_neg hc, h_px]
          omega
        have h_A2_px : (A2 h hh (pred2c h hh x)).val = 1 := by
          rw [h_A2_val]
          have hc : ¬((y2star h hh (pred2c h hh x)).val = 2 * h - 1) := by rw [h_y2_px]; omega
          rw [if_neg hc, h_y2_px]
        have h_y2_x : (y2star h hh x).val = 2 * h - 1 := by
          rw [h_y2_val]
          have hc : ¬(x.val = h + 1 ∨ x.val = h + 2 ∨ x.val = h + 3) := by omega
          rw [if_neg hc]
          omega
        have h_A2_x : (A2 h hh x).val = 0 := by
          rw [h_A2_val]
          have hc : (y2star h hh x).val = 2 * h - 1 := by rw [h_y2_x]
          rw [if_pos hc]
        have h_LHS : (if (A2 h hh x).val = 2 * h - 1 then 0 else (A2 h hh x).val + 1) = 1 := by
          have hc : ¬((A2 h hh x).val = 2 * h - 1) := by rw [h_A2_x]; omega
          rw [if_neg hc, h_A2_x]
        have h_H : (if (pred2c h hh x).val = h + 1 ∨ (pred2c h hh x).val = h + 2 then (A2 h hh (pred2c h hh x)).val else (pred2c h hh (A2 h hh (pred2c h hh x))).val) = 0 := by
          have hc : ¬((pred2c h hh x).val = h + 1 ∨ (pred2c h hh x).val = h + 2) := by rw [h_px]; omega
          rw [if_neg hc, h_pz]
          have hc2 : ¬((A2 h hh (pred2c h hh x)).val = 0) := by rw [h_A2_px]; omega
          rw [if_neg hc2, h_A2_px]
        have h_RHS : (if (if (pred2c h hh x).val = h + 1 ∨ (pred2c h hh x).val = h + 2 then (A2 h hh (pred2c h hh x)).val else (pred2c h hh (A2 h hh (pred2c h hh x))).val) = 2 * h - 1 then 0 else (if (pred2c h hh x).val = h + 1 ∨ (pred2c h hh x).val = h + 2 then (A2 h hh (pred2c h hh x)).val else (pred2c h hh (A2 h hh (pred2c h hh x))).val) + 1) = 1 := by
          have hc : ¬((if (pred2c h hh x).val = h + 1 ∨ (pred2c h hh x).val = h + 2 then (A2 h hh (pred2c h hh x)).val else (pred2c h hh (A2 h hh (pred2c h hh x))).val) = 2 * h - 1) := by rw [h_H]; omega
          rw [if_neg hc, h_H]
        rw [h_LHS, h_RHS]
      · have h_px : (pred2c h hh x).val = 0 := by
          rw [h_pz]
          have hc : ¬(x.val = 0) := by omega
          rw [if_neg hc]
          omega
        have h_y2_px : (y2star h hh (pred2c h hh x)).val = 2 * h - 1 := by
          rw [h_y2_val]
          have hc : ¬((pred2c h hh x).val = h + 1 ∨ (pred2c h hh x).val = h + 2 ∨ (pred2c h hh x).val = h + 3) := by rw [h_px]; omega
          rw [if_neg hc, h_px]
          omega
        have h_A2_px : (A2 h hh (pred2c h hh x)).val = 0 := by
          rw [h_A2_val]
          have hc : (y2star h hh (pred2c h hh x)).val = 2 * h - 1 := by rw [h_y2_px]
          rw [if_pos hc]
        have h_y2_x : (y2star h hh x).val = 2 * h - 2 := by
          rw [h_y2_val]
          have hc : ¬(x.val = h + 1 ∨ x.val = h + 2 ∨ x.val = h + 3) := by omega
          rw [if_neg hc]
          omega
        have h_A2_x : (A2 h hh x).val = 2 * h - 1 := by
          rw [h_A2_val]
          have hc : ¬((y2star h hh x).val = 2 * h - 1) := by rw [h_y2_x]; omega
          rw [if_neg hc, h_y2_x]
          omega
        have h_LHS : (if (A2 h hh x).val = 2 * h - 1 then 0 else (A2 h hh x).val + 1) = 0 := by
          have hc : (A2 h hh x).val = 2 * h - 1 := by rw [h_A2_x]
          rw [if_pos hc]
        have h_H : (if (pred2c h hh x).val = h + 1 ∨ (pred2c h hh x).val = h + 2 then (A2 h hh (pred2c h hh x)).val else (pred2c h hh (A2 h hh (pred2c h hh x))).val) = 2 * h - 1 := by
          have hc : ¬((pred2c h hh x).val = h + 1 ∨ (pred2c h hh x).val = h + 2) := by rw [h_px]; omega
          rw [if_neg hc, h_pz]
          have hc2 : (A2 h hh (pred2c h hh x)).val = 0 := by rw [h_A2_px]
          rw [if_pos hc2]
        have h_RHS : (if (if (pred2c h hh x).val = h + 1 ∨ (pred2c h hh x).val = h + 2 then (A2 h hh (pred2c h hh x)).val else (pred2c h hh (A2 h hh (pred2c h hh x))).val) = 2 * h - 1 then 0 else (if (pred2c h hh x).val = h + 1 ∨ (pred2c h hh x).val = h + 2 then (A2 h hh (pred2c h hh x)).val else (pred2c h hh (A2 h hh (pred2c h hh x))).val) + 1) = 0 := by
          have hc : (if (pred2c h hh x).val = h + 1 ∨ (pred2c h hh x).val = h + 2 then (A2 h hh (pred2c h hh x)).val else (pred2c h hh (A2 h hh (pred2c h hh x))).val) = 2 * h - 1 := by rw [h_H]
          rw [if_pos hc]
        rw [h_LHS, h_RHS]
      · have h_px : (pred2c h hh x).val = h + 1 := by
          rw [h_pz]
          have hc : ¬(x.val = 0) := by omega
          rw [if_neg hc]
          omega
        rcases eq_or_ne (h % 2) 0 with h_mod | h_mod
        · have h_y2_px : (y2star h hh (pred2c h hh x)).val = 2 * h - 2 := by
            rw [h_y2_val]
            have hc : (pred2c h hh x).val = h + 1 ∨ (pred2c h hh x).val = h + 2 ∨ (pred2c h hh x).val = h + 3 := by rw [h_px]; omega
            rw [if_pos hc]
            have hc2 : h % 2 = 0 := h_mod
            rw [if_pos hc2]
          have h_A2_px : (A2 h hh (pred2c h hh x)).val = 2 * h - 1 := by
            rw [h_A2_val]
            have hc : ¬((y2star h hh (pred2c h hh x)).val = 2 * h - 1) := by rw [h_y2_px]; omega
            rw [if_neg hc, h_y2_px]
            omega
          have h_y2_x : (y2star h hh x).val = 2 * h - 2 := by
            rw [h_y2_val]
            have hc : x.val = h + 1 ∨ x.val = h + 2 ∨ x.val = h + 3 := by omega
            rw [if_pos hc]
            have hc2 : h % 2 = 0 := h_mod
            rw [if_pos hc2]
          have h_A2_x : (A2 h hh x).val = 2 * h - 1 := by
            rw [h_A2_val]
            have hc : ¬((y2star h hh x).val = 2 * h - 1) := by rw [h_y2_x]; omega
            rw [if_neg hc, h_y2_x]
            omega
          have h_LHS : (if (A2 h hh x).val = 2 * h - 1 then 0 else (A2 h hh x).val + 1) = 0 := by
            have hc : (A2 h hh x).val = 2 * h - 1 := by rw [h_A2_x]
            rw [if_pos hc]
          have h_H : (if (pred2c h hh x).val = h + 1 ∨ (pred2c h hh x).val = h + 2 then (A2 h hh (pred2c h hh x)).val else (pred2c h hh (A2 h hh (pred2c h hh x))).val) = 2 * h - 1 := by
            have hc : (pred2c h hh x).val = h + 1 ∨ (pred2c h hh x).val = h + 2 := by rw [h_px]; omega
            rw [if_pos hc, h_A2_px]
          have h_RHS : (if (if (pred2c h hh x).val = h + 1 ∨ (pred2c h hh x).val = h + 2 then (A2 h hh (pred2c h hh x)).val else (pred2c h hh (A2 h hh (pred2c h hh x))).val) = 2 * h - 1 then 0 else (if (pred2c h hh x).val = h + 1 ∨ (pred2c h hh x).val = h + 2 then (A2 h hh (pred2c h hh x)).val else (pred2c h hh (A2 h hh (pred2c h hh x))).val) + 1) = 0 := by
            have hc : (if (pred2c h hh x).val = h + 1 ∨ (pred2c h hh x).val = h + 2 then (A2 h hh (pred2c h hh x)).val else (pred2c h hh (A2 h hh (pred2c h hh x))).val) = 2 * h - 1 := by rw [h_H]
            rw [if_pos hc]
          rw [h_LHS, h_RHS]
        · have h_y2_px : (y2star h hh (pred2c h hh x)).val = 2 * h - 1 := by
            rw [h_y2_val]
            have hc : (pred2c h hh x).val = h + 1 ∨ (pred2c h hh x).val = h + 2 ∨ (pred2c h hh x).val = h + 3 := by rw [h_px]; omega
            rw [if_pos hc]
            have hc2 : ¬(h % 2 = 0) := h_mod
            rw [if_neg hc2]
          have h_A2_px : (A2 h hh (pred2c h hh x)).val = 0 := by
            rw [h_A2_val]
            have hc : (y2star h hh (pred2c h hh x)).val = 2 * h - 1 := by rw [h_y2_px]
            rw [if_pos hc]
          have h_y2_x : (y2star h hh x).val = 2 * h - 1 := by
            rw [h_y2_val]
            have hc : x.val = h + 1 ∨ x.val = h + 2 ∨ x.val = h + 3 := by omega
            rw [if_pos hc]
            have hc2 : ¬(h % 2 = 0) := h_mod
            rw [if_neg hc2]
          have h_A2_x : (A2 h hh x).val = 0 := by
            rw [h_A2_val]
            have hc : (y2star h hh x).val = 2 * h - 1 := by rw [h_y2_x]
            rw [if_pos hc]
          have h_LHS : (if (A2 h hh x).val = 2 * h - 1 then 0 else (A2 h hh x).val + 1) = 1 := by
            have hc : ¬((A2 h hh x).val = 2 * h - 1) := by rw [h_A2_x]; omega
            rw [if_neg hc, h_A2_x]
          have h_H : (if (pred2c h hh x).val = h + 1 ∨ (pred2c h hh x).val = h + 2 then (A2 h hh (pred2c h hh x)).val else (pred2c h hh (A2 h hh (pred2c h hh x))).val) = 0 := by
            have hc : (pred2c h hh x).val = h + 1 ∨ (pred2c h hh x).val = h + 2 := by rw [h_px]; omega
            rw [if_pos hc, h_A2_px]
          have h_RHS : (if (if (pred2c h hh x).val = h + 1 ∨ (pred2c h hh x).val = h + 2 then (A2 h hh (pred2c h hh x)).val else (pred2c h hh (A2 h hh (pred2c h hh x))).val) = 2 * h - 1 then 0 else (if (pred2c h hh x).val = h + 1 ∨ (pred2c h hh x).val = h + 2 then (A2 h hh (pred2c h hh x)).val else (pred2c h hh (A2 h hh (pred2c h hh x))).val) + 1) = 1 := by
            have hc : ¬((if (pred2c h hh x).val = h + 1 ∨ (pred2c h hh x).val = h + 2 then (A2 h hh (pred2c h hh x)).val else (pred2c h hh (A2 h hh (pred2c h hh x))).val) = 2 * h - 1) := by rw [h_H]; omega
            rw [if_neg hc, h_H]
          rw [h_LHS, h_RHS]
      · have h_px : (pred2c h hh x).val = h + 2 := by
          rw [h_pz]
          have hc : ¬(x.val = 0) := by omega
          rw [if_neg hc]
          omega
        rcases eq_or_ne (h % 2) 0 with h_mod | h_mod
        · have h_y2_px : (y2star h hh (pred2c h hh x)).val = 2 * h - 2 := by
            rw [h_y2_val]
            have hc : (pred2c h hh x).val = h + 1 ∨ (pred2c h hh x).val = h + 2 ∨ (pred2c h hh x).val = h + 3 := by rw [h_px]; omega
            rw [if_pos hc]
            have hc2 : h % 2 = 0 := h_mod
            rw [if_pos hc2]
          have h_A2_px : (A2 h hh (pred2c h hh x)).val = 2 * h - 1 := by
            rw [h_A2_val]
            have hc : ¬((y2star h hh (pred2c h hh x)).val = 2 * h - 1) := by rw [h_y2_px]; omega
            rw [if_neg hc, h_y2_px]
            omega
          have h_y2_x : (y2star h hh x).val = 2 * h - 2 := by
            rw [h_y2_val]
            have hc : x.val = h + 1 ∨ x.val = h + 2 ∨ x.val = h + 3 := by omega
            rw [if_pos hc]
            have hc2 : h % 2 = 0 := h_mod
            rw [if_pos hc2]
          have h_A2_x : (A2 h hh x).val = 2 * h - 1 := by
            rw [h_A2_val]
            have hc : ¬((y2star h hh x).val = 2 * h - 1) := by rw [h_y2_x]; omega
            rw [if_neg hc, h_y2_x]
            omega
          have h_LHS : (if (A2 h hh x).val = 2 * h - 1 then 0 else (A2 h hh x).val + 1) = 0 := by
            have hc : (A2 h hh x).val = 2 * h - 1 := by rw [h_A2_x]
            rw [if_pos hc]
          have h_H : (if (pred2c h hh x).val = h + 1 ∨ (pred2c h hh x).val = h + 2 then (A2 h hh (pred2c h hh x)).val else (pred2c h hh (A2 h hh (pred2c h hh x))).val) = 2 * h - 1 := by
            have hc : (pred2c h hh x).val = h + 1 ∨ (pred2c h hh x).val = h + 2 := by rw [h_px]; omega
            rw [if_pos hc, h_A2_px]
          have h_RHS : (if (if (pred2c h hh x).val = h + 1 ∨ (pred2c h hh x).val = h + 2 then (A2 h hh (pred2c h hh x)).val else (pred2c h hh (A2 h hh (pred2c h hh x))).val) = 2 * h - 1 then 0 else (if (pred2c h hh x).val = h + 1 ∨ (pred2c h hh x).val = h + 2 then (A2 h hh (pred2c h hh x)).val else (pred2c h hh (A2 h hh (pred2c h hh x))).val) + 1) = 0 := by
            have hc : (if (pred2c h hh x).val = h + 1 ∨ (pred2c h hh x).val = h + 2 then (A2 h hh (pred2c h hh x)).val else (pred2c h hh (A2 h hh (pred2c h hh x))).val) = 2 * h - 1 := by rw [h_H]
            rw [if_pos hc]
          rw [h_LHS, h_RHS]
        · have h_y2_px : (y2star h hh (pred2c h hh x)).val = 2 * h - 1 := by
            rw [h_y2_val]
            have hc : (pred2c h hh x).val = h + 1 ∨ (pred2c h hh x).val = h + 2 ∨ (pred2c h hh x).val = h + 3 := by rw [h_px]; omega
            rw [if_pos hc]
            have hc2 : ¬(h % 2 = 0) := h_mod
            rw [if_neg hc2]
          have h_A2_px : (A2 h hh (pred2c h hh x)).val = 0 := by
            rw [h_A2_val]
            have hc : (y2star h hh (pred2c h hh x)).val = 2 * h - 1 := by rw [h_y2_px]
            rw [if_pos hc]
          have h_y2_x : (y2star h hh x).val = 2 * h - 1 := by
            rw [h_y2_val]
            have hc : x.val = h + 1 ∨ x.val = h + 2 ∨ x.val = h + 3 := by omega
            rw [if_pos hc]
            have hc2 : ¬(h % 2 = 0) := h_mod
            rw [if_neg hc2]
          have h_A2_x : (A2 h hh x).val = 0 := by
            rw [h_A2_val]
            have hc : (y2star h hh x).val = 2 * h - 1 := by rw [h_y2_x]
            rw [if_pos hc]
          have h_LHS : (if (A2 h hh x).val = 2 * h - 1 then 0 else (A2 h hh x).val + 1) = 1 := by
            have hc : ¬((A2 h hh x).val = 2 * h - 1) := by rw [h_A2_x]; omega
            rw [if_neg hc, h_A2_x]
          have h_H : (if (pred2c h hh x).val = h + 1 ∨ (pred2c h hh x).val = h + 2 then (A2 h hh (pred2c h hh x)).val else (pred2c h hh (A2 h hh (pred2c h hh x))).val) = 0 := by
            have hc : (pred2c h hh x).val = h + 1 ∨ (pred2c h hh x).val = h + 2 := by rw [h_px]; omega
            rw [if_pos hc, h_A2_px]
          have h_RHS : (if (if (pred2c h hh x).val = h + 1 ∨ (pred2c h hh x).val = h + 2 then (A2 h hh (pred2c h hh x)).val else (pred2c h hh (A2 h hh (pred2c h hh x))).val) = 2 * h - 1 then 0 else (if (pred2c h hh x).val = h + 1 ∨ (pred2c h hh x).val = h + 2 then (A2 h hh (pred2c h hh x)).val else (pred2c h hh (A2 h hh (pred2c h hh x))).val) + 1) = 1 := by
            have hc : ¬((if (pred2c h hh x).val = h + 1 ∨ (pred2c h hh x).val = h + 2 then (A2 h hh (pred2c h hh x)).val else (pred2c h hh (A2 h hh (pred2c h hh x))).val) = 2 * h - 1) := by rw [h_H]; omega
            rw [if_neg hc, h_H]
          rw [h_LHS, h_RHS]
      · rcases h_other with ⟨hx0_ne, hx1_ne, hx2_ne, hx3_ne⟩
        have h_px : (pred2c h hh x).val = x.val - 1 := by
          rw [h_pz]
          have hc : ¬(x.val = 0) := by omega
          rw [if_neg hc]
        have h_y2_px : (y2star h hh (pred2c h hh x)).val = 2 * h - x.val := by
          rw [h_y2_val]
          have hc : ¬((pred2c h hh x).val = h + 1 ∨ (pred2c h hh x).val = h + 2 ∨ (pred2c h hh x).val = h + 3) := by
            intro h_false
            rcases h_false with h_false | h_false | h_false
            · rw [h_px] at h_false; omega
            · rw [h_px] at h_false; omega
            · rw [h_px] at h_false; omega
          rw [if_neg hc, h_px]
          omega
        have h_A2_px : (A2 h hh (pred2c h hh x)).val = 2 * h - x.val + 1 := by
          rw [h_A2_val]
          have hc : ¬((y2star h hh (pred2c h hh x)).val = 2 * h - 1) := by rw [h_y2_px]; omega
          rw [if_neg hc, h_y2_px]
        have h_y2_x : (y2star h hh x).val = 2 * h - 1 - x.val := by
          rw [h_y2_val]
          have hc : ¬(x.val = h + 1 ∨ x.val = h + 2 ∨ x.val = h + 3) := by omega
          rw [if_neg hc]
        have h_A2_x : (A2 h hh x).val = 2 * h - x.val := by
          rw [h_A2_val]
          have hc : ¬((y2star h hh x).val = 2 * h - 1) := by rw [h_y2_x]; omega
          rw [if_neg hc, h_y2_x]
          omega
        have h_LHS : (if (A2 h hh x).val = 2 * h - 1 then 0 else (A2 h hh x).val + 1) = 2 * h - x.val + 1 := by
          have hc : ¬((A2 h hh x).val = 2 * h - 1) := by rw [h_A2_x]; omega
          rw [if_neg hc, h_A2_x]
        have h_H : (if (pred2c h hh x).val = h + 1 ∨ (pred2c h hh x).val = h + 2 then (A2 h hh (pred2c h hh x)).val else (pred2c h hh (A2 h hh (pred2c h hh x))).val) = 2 * h - x.val := by
          have hc : ¬((pred2c h hh x).val = h + 1 ∨ (pred2c h hh x).val = h + 2) := by
            intro h_false
            rcases h_false with h_false | h_false
            · rw [h_px] at h_false; omega
            · rw [h_px] at h_false; omega
          rw [if_neg hc, h_pz]
          have hc2 : ¬((A2 h hh (pred2c h hh x)).val = 0) := by rw [h_A2_px]; omega
          rw [if_neg hc2, h_A2_px]
          omega
        have h_RHS : (if (if (pred2c h hh x).val = h + 1 ∨ (pred2c h hh x).val = h + 2 then (A2 h hh (pred2c h hh x)).val else (pred2c h hh (A2 h hh (pred2c h hh x))).val) = 2 * h - 1 then 0 else (if (pred2c h hh x).val = h + 1 ∨ (pred2c h hh x).val = h + 2 then (A2 h hh (pred2c h hh x)).val else (pred2c h hh (A2 h hh (pred2c h hh x))).val) + 1) = 2 * h - x.val + 1 := by
          have hc : ¬((if (pred2c h hh x).val = h + 1 ∨ (pred2c h hh x).val = h + 2 then (A2 h hh (pred2c h hh x)).val else (pred2c h hh (A2 h hh (pred2c h hh x))).val) = 2 * h - 1) := by rw [h_H]; omega
          rw [if_neg hc, h_H]
        rw [h_LHS, h_RHS]

    have h_not_jump : H_val h hh x - natToFin h hh k ≠ jump_y h hh x := by
      intro heq
      have heq2 : H_val h hh x - natToFin h hh k + natToFin h hh k = jump_y h hh x + natToFin h hh k := congrArg (· + natToFin h hh k) heq
      rw [sub_add_cancel, hj_fin, add_assoc] at heq2
      have heq3 : (H_val h hh x).val = (H_val h hh x + (one2 h hh + natToFin h hh k)).val := congrArg Fin.val heq2
      rw [Fin.val_add] at heq3
      have hk_add : (one2 h hh + natToFin h hh k).val = k + 1 := by
        rw [Fin.val_add]
        have h1_val : (one2 h hh).val = 1 := rfl
        have hk_val : (natToFin h hh k).val = k := Nat.mod_eq_of_lt (by omega)
        rw [h1_val, hk_val, add_comm]
        exact Nat.mod_eq_of_lt (by omega)
      rw [hk_add] at heq3
      have h_mod_cases : ((H_val h hh x).val + (k + 1)) % (2 * h) = if (H_val h hh x).val + (k + 1) < 2 * h then (H_val h hh x).val + (k + 1) else (H_val h hh x).val + (k + 1) - 2 * h := by
        split_ifs with h_lt2
        · exact Nat.mod_eq_of_lt h_lt2
        · have h_sub : (H_val h hh x).val + (k + 1) - 2 * h < 2 * h := by
            have : (H_val h hh x).val < 2 * h := (H_val h hh x).isLt
            omega
          have h_step : ((H_val h hh x).val + (k + 1)) % (2 * h) = ((H_val h hh x).val + (k + 1) - 2 * h) % (2 * h) := by
            have heq : (H_val h hh x).val + (k + 1) = (H_val h hh x).val + (k + 1) - 2 * h + 2 * h := by omega
            have h_eq_mod : ((H_val h hh x).val + (k + 1)) % (2 * h) = ((H_val h hh x).val + (k + 1) - 2 * h + 2 * h) % (2 * h) := congrArg (· % (2 * h)) heq
            rw [h_eq_mod, Nat.add_mod_right]
          rw [h_step]
          exact Nat.mod_eq_of_lt h_sub
      rw [h_mod_cases] at heq3
      split_ifs at heq3 <;> omega

    rw [if_neg h_not_jump]

    have h_not_active : ¬ activeB2 h x (pred2c h hh (H_val h hh x - natToFin h hh k)) := h_gen _
    rw [if_neg h_not_active]

    have h_eq : pred2c h hh (H_val h hh x - natToFin h hh k) = H_val h hh x - natToFin h hh (k + 1) := by
      unfold pred2c
      have h_k_add : natToFin h hh (k + 1) = natToFin h hh k + one2 h hh := by
        ext
        have h_one_val : (one2 h hh).val = 1 := rfl
        have h_k_val : (natToFin h hh k).val = k := Nat.mod_eq_of_lt (by omega)
        have h_k1_val : (natToFin h hh (k + 1)).val = k + 1 := Nat.mod_eq_of_lt (by omega)
        have eq_add := Fin.val_add (natToFin h hh k) (one2 h hh)
        rw [eq_add, h_one_val, h_k_val, h_k1_val]
        exact (Nat.mod_eq_of_lt (by omega)).symm
      rw [h_k_add, sub_add_eq_sub_sub]

    exact h_eq

theorem row_map_generic_not_jump (x : Fin (2 * h)) (h_gen : ∀ y, ¬ activeB2 h x y) (k : ℕ) (hk : k < 2 * h - 1) :
  (row_map h hh x)^[k] (H_val h hh x) ≠ jump_y h hh x :=
by
  have hk_le : k ≤ 2 * h - 1 := by omega
  rw [row_map_generic_iter h hh x h_gen k hk_le]
  exact H_val_sub_not_jump h hh x h_gen k hk

theorem exists_minimal_k (h : ℕ) (hh : 5 ≤ h) (x : Fin (2 * h)) (k : ℕ)
  (hk : (row_map h hh x)^[k] (H_val h hh x) = jump_y h hh x) :
  ∃ k_min ≤ k, (row_map h hh x)^[k_min] (H_val h hh x) = jump_y h hh x ∧
    ∀ j < k_min, (row_map h hh x)^[j] (H_val h hh x) ≠ jump_y h hh x :=
by
  have ex : ∃ n, (row_map h hh x)^[n] (H_val h hh x) = jump_y h hh x := ⟨k, hk⟩
  exact ⟨Nat.find ex, Nat.find_min' ex hk, Nat.find_spec ex, fun j hj => Nat.find_min ex hj⟩

theorem total_desc_eq_c (h : ℕ) (hh : 5 ≤ h) (x : Fin (2 * h)) (h_act : ∃ y, activeB2 h x y) (k : ℕ)
  (hk_jump : (row_map h hh x)^[k] (H_val h hh x) = jump_y h hh x)
  (hk_min : ∀ j < k, (row_map h hh x)^[j] (H_val h hh x) ≠ jump_y h hh x) :
  ∃ c : ℤ, c ≥ 0 ∧ (total_desc h hh x k : ℤ) = c * (2 * (h : ℤ)) + H_sub_J h hh x :=
by
  have hn : 0 < 2 * h := by omega
  haveI : NeZero (2 * h) := ⟨by omega⟩

  have natToFin_add : ∀ a b, natToFin h hh (a + b) = natToFin h hh a + natToFin h hh b := by
    intro a b
    apply Fin.ext
    exact Nat.add_mod a b (2 * h)

  have natToFin_zero : natToFin h hh 0 = 0 := by
    apply Fin.ext
    rfl

  have natToFin_val : ∀ z : Fin (2 * h), natToFin h hh z.val = z := by
    intro z
    apply Fin.ext
    exact Nat.mod_eq_of_lt z.isLt

  have h_pred_add : ∀ z : Fin (2 * h), pred2c h hh z + natToFin h hh 1 = z := by
    intro z
    unfold pred2c
    have h_one_eq : one2 h hh = natToFin h hh 1 := by
      apply Fin.ext
      exact (Nat.mod_eq_of_lt (by omega)).symm
    rw [h_one_eq]
    exact sub_add_cancel z (natToFin h hh 1)

  have H_row_map : ∀ y, y ≠ jump_y h hh x →
      y = row_map h hh x y + natToFin h hh (step_desc h hh x y) := by
    intro y hy
    unfold row_map step_desc
    have h_not : ¬ (y = jump_y h hh x) := hy
    simp only [h_not, ↓reduceIte]
    split_ifs with h2
    · have h_two : natToFin h hh 2 = natToFin h hh 1 + natToFin h hh 1 := by
        have h_add := natToFin_add 1 1
        exact h_add
      rw [h_two]
      rw [← add_assoc]
      rw [h_pred_add (pred2c h hh y)]
      rw [h_pred_add y]
    · exact (h_pred_add y).symm

  have H_mod_step : ∀ n, n ≤ k → H_val h hh x = (row_map h hh x)^[n] (H_val h hh x) + natToFin h hh (total_desc h hh x n) := by
    intro n
    induction' n with m ihm
    · intro _
      have h_zero : total_desc h hh x 0 = 0 := rfl
      rw [h_zero, natToFin_zero]
      exact (add_zero _).symm
    · intro hm
      have hm_lt : m < k := by omega
      have hm_le : m ≤ k := by omega
      have hy_neq : (row_map h hh x)^[m] (H_val h hh x) ≠ jump_y h hh x := hk_min m hm_lt
      have h_row := H_row_map ((row_map h hh x)^[m] (H_val h hh x)) hy_neq
      rw [Function.iterate_succ_apply']
      have h_tot : total_desc h hh x (m + 1) = total_desc h hh x m + step_desc h hh x ((row_map h hh x)^[m] (H_val h hh x)) := rfl
      rw [h_tot]
      rw [natToFin_add]
      rw [add_comm (natToFin h hh (total_desc h hh x m))]
      rw [← add_assoc]
      rw [← h_row]
      exact ihm hm_le

  have hk_eq3 : natToFin h hh (total_desc h hh x k) + jump_y h hh x = H_val h hh x := by
    have h_mod := H_mod_step k (by omega)
    rw [hk_jump] at h_mod
    rw [add_comm] at h_mod
    exact h_mod.symm

  have hk_eq_fin : natToFin h hh (total_desc h hh x k + (jump_y h hh x).val) = H_val h hh x := by
    rw [natToFin_add]
    rw [natToFin_val]
    exact hk_eq3

  have hk_mod_eq2 : (total_desc h hh x k + (jump_y h hh x).val) % (2 * h) = (H_val h hh x).val := by
    have h_val := congrArg Fin.val hk_eq_fin
    dsimp [natToFin] at h_val
    exact h_val

  have h_div_mod := Nat.div_add_mod (total_desc h hh x k + (jump_y h hh x).val) (2 * h)
  have h_sub : (total_desc h hh x k + (jump_y h hh x).val) % (2 * h) = (H_val h hh x).val := hk_mod_eq2
  rw [h_sub] at h_div_mod

  let c_nat := (total_desc h hh x k + (jump_y h hh x).val) / (2 * h)
  use (c_nat : ℤ)
  constructor
  · exact Nat.cast_nonneg _
  · unfold H_sub_J
    have h_c_nat : (total_desc h hh x k + (jump_y h hh x).val) / (2 * h) = c_nat := rfl
    rw [h_c_nat] at h_div_mod
    zify at h_div_mod ⊢
    have h_mul_comm : (c_nat : ℤ) * (2 * (h : ℤ)) = (2 * (h : ℤ)) * (c_nat : ℤ) := mul_comm _ _
    rw [h_mul_comm]
    linarith

theorem trajectory_distinct_of_min_jump (h : ℕ) (hh : 5 ≤ h) (x : Fin (2 * h)) (k : ℕ)
  (hk_jump : (row_map h hh x)^[k] (H_val h hh x) = jump_y h hh x)
  (hk_min : ∀ j < k, (row_map h hh x)^[j] (H_val h hh x) ≠ jump_y h hh x)
  (i j : ℕ) (hi : i < k) (hj : j < k) (hij : i ≠ j) :
  (row_map h hh x)^[i] (H_val h hh x) ≠ (row_map h hh x)^[j] (H_val h hh x) :=
by
  intro h_eq
  have h_cases : i < j ∨ j < i := by omega
  rcases h_cases with hij_lt | hij_gt
  · let m := k - j + i
    have hm_lt : m < k := by omega
    have h_k_eq_m : (row_map h hh x)^[m] (H_val h hh x) = (row_map h hh x)^[k] (H_val h hh x) := by
      calc (row_map h hh x)^[m] (H_val h hh x)
        _ = (row_map h hh x)^[k - j + i] (H_val h hh x) := rfl
        _ = (row_map h hh x)^[k - j] ((row_map h hh x)^[i] (H_val h hh x)) := by rw [Function.iterate_add_apply]
        _ = (row_map h hh x)^[k - j] ((row_map h hh x)^[j] (H_val h hh x)) := by rw [h_eq]
        _ = (row_map h hh x)^[k - j + j] (H_val h hh x) := by rw [← Function.iterate_add_apply]
        _ = (row_map h hh x)^[k] (H_val h hh x) := by
          have h_eq_k : k - j + j = k := by omega
          rw [h_eq_k]
    rw [hk_jump] at h_k_eq_m
    exact hk_min m hm_lt h_k_eq_m
  · let m := k - i + j
    have hm_lt : m < k := by omega
    have h_k_eq_m : (row_map h hh x)^[m] (H_val h hh x) = (row_map h hh x)^[k] (H_val h hh x) := by
      calc (row_map h hh x)^[m] (H_val h hh x)
        _ = (row_map h hh x)^[k - i + j] (H_val h hh x) := rfl
        _ = (row_map h hh x)^[k - i] ((row_map h hh x)^[j] (H_val h hh x)) := by rw [Function.iterate_add_apply]
        _ = (row_map h hh x)^[k - i] ((row_map h hh x)^[i] (H_val h hh x)) := by rw [← h_eq]
        _ = (row_map h hh x)^[k - i + i] (H_val h hh x) := by rw [← Function.iterate_add_apply]
        _ = (row_map h hh x)^[k] (H_val h hh x) := by
          have h_eq_k : k - i + i = k := by omega
          rw [h_eq_k]
    rw [hk_jump] at h_k_eq_m
    exact hk_min m hm_lt h_k_eq_m

theorem total_desc_eq_k_plus_N_active_Z (h : ℕ) (hh : 5 ≤ h) (x : Fin (2 * h)) (k : ℕ) :
  (total_desc h hh x k : ℤ) = (k : ℤ) + (N_active h hh x k : ℤ) :=
by
  induction k with
  | zero =>
    have ht : total_desc h hh x 0 = 0 := rfl
    have hn : N_active h hh x 0 = 0 := rfl
    rw [ht, hn]
    omega
  | succ d hd =>
    have ht : total_desc h hh x (Nat.succ d) = total_desc h hh x d + step_desc h hh x ((row_map h hh x)^[d] (H_val h hh x)) := rfl
    have hn : N_active h hh x (Nat.succ d) = N_active h hh x d + is_active_step h hh x ((row_map h hh x)^[d] (H_val h hh x)) := rfl
    rw [ht, hn]
    push_cast
    rw [hd]
    unfold step_desc is_active_step
    split_ifs
    · omega
    · omega

theorem active_Icc_card_eq (h : ℕ) (hh : 5 ≤ h) (x : Fin (2 * h)) (h_act : ∃ y, activeB2 h x y) :
  (Finset.Icc (a_act h hh x).val (b_act h hh x).val).card = L_act h hh x + 1 :=
by
  rw [Nat.card_Icc]
  dsimp [a_act, b_act, L_act]
  split_ifs <;> dsimp <;> omega

theorem N_active_eq_card_filter (h : ℕ) (hh : 5 ≤ h) (x : Fin (2 * h)) (k : ℕ) :
  N_active h hh x k = (Finset.filter (fun i => activeB2 h x (pred2c h hh ((row_map h hh x)^[i] (H_val h hh x)))) (Finset.range k)).card :=
by
  induction k with
  | zero => rfl
  | succ n ih =>
    change N_active h hh x n + is_active_step h hh x ((row_map h hh x)^[n] (H_val h hh x)) = _
    rw [ih, Finset.range_succ]
    simp only [Finset.filter_insert]
    have h_not_mem : n ∉ Finset.filter (fun i => activeB2 h x (pred2c h hh ((row_map h hh x)^[i] (H_val h hh x)))) (Finset.range n) := by
      intro h_mem
      rw [Finset.mem_filter, Finset.mem_range] at h_mem
      omega
    unfold is_active_step
    split_ifs
    · rw [Finset.card_insert_of_notMem h_not_mem]
    · omega

theorem N_active_maps_to_Icc (h : ℕ) (hh : 5 ≤ h) (x : Fin (2 * h)) (h_act : ∃ y, activeB2 h x y) (k : ℕ) :
  ∀ i ∈ (Finset.filter (fun i => activeB2 h x (pred2c h hh ((row_map h hh x)^[i] (H_val h hh x)))) (Finset.range k)),
    (pred2c h hh ((row_map h hh x)^[i] (H_val h hh x))).val ∈ Finset.Icc (a_act h hh x).val (b_act h hh x).val :=
by
  intro i hi
  rw [Finset.mem_filter] at hi
  generalize pred2c h hh ((row_map h hh x)^[i] (H_val h hh x)) = y at hi ⊢
  have hy : activeB2 h x y := hi.2
  have y_lt : y.val < 2 * h := y.isLt
  rw [Finset.mem_Icc]
  unfold activeB2 at hy
  split_ifs at hy with h_mod
  · rcases hy with ⟨hx_eq, hy_le⟩ | ⟨hx_eq, hy_ge, hy_le⟩
    · simp [a_act, b_act, hx_eq, h_mod]; omega
    · simp [a_act, b_act, hx_eq, h_mod]; omega
  · rcases hy with ⟨hx_eq, hy_ge, hy_le⟩ | ⟨hx_eq, hy_ge⟩
    · simp [a_act, b_act, hx_eq, h_mod]; omega
    · simp [a_act, b_act, hx_eq, h_mod]; omega

theorem N_active_inj_on_filter (h : ℕ) (hh : 5 ≤ h) (x : Fin (2 * h)) (k : ℕ)
  (h_distinct : ∀ i j, i < k → j < k → i ≠ j → (row_map h hh x)^[i] (H_val h hh x) ≠ (row_map h hh x)^[j] (H_val h hh x)) :
  ∀ i ∈ (Finset.filter (fun i => activeB2 h x (pred2c h hh ((row_map h hh x)^[i] (H_val h hh x)))) (Finset.range k)),
  ∀ j ∈ (Finset.filter (fun i => activeB2 h x (pred2c h hh ((row_map h hh x)^[i] (H_val h hh x)))) (Finset.range k)),
  (pred2c h hh ((row_map h hh x)^[i] (H_val h hh x))).val = (pred2c h hh ((row_map h hh x)^[j] (H_val h hh x))).val →
  i = j :=
by
  intros i hi j hj heq
  rw [Finset.mem_filter, Finset.mem_range] at hi hj
  have hik : i < k := hi.1
  have hjk : j < k := hj.1

  -- Ensure Fin (2 * h) meets the NeZero requirement locally for the AddGroup typeclass (needed by sub_add_cancel).
  have h_ne_zero : 2 * h ≠ 0 := by omega
  haveI : NeZero (2 * h) := ⟨h_ne_zero⟩

  have heq2 : pred2c h hh ((row_map h hh x)^[i] (H_val h hh x)) = pred2c h hh ((row_map h hh x)^[j] (H_val h hh x)) := Fin.ext heq
  have heq3 : (row_map h hh x)^[i] (H_val h hh x) = (row_map h hh x)^[j] (H_val h hh x) := by
    have h_add := congrArg (fun u => u + one2 h hh) heq2
    dsimp [pred2c] at h_add
    have h_cancel : ∀ u : Fin (2 * h), u - one2 h hh + one2 h hh = u := by
      intro u
      first
      | exact sub_add_cancel u (one2 h hh)
      | apply Fin.ext; omega
    rw [h_cancel, h_cancel] at h_add
    exact h_add

  by_contra h_neq
  have h_diff := h_distinct i j hik hjk h_neq
  exact h_diff heq3

theorem N_active_le_Icc_card (h : ℕ) (hh : 5 ≤ h) (x : Fin (2 * h)) (h_act : ∃ y, activeB2 h x y) (k : ℕ)
  (h_distinct : ∀ i j, i < k → j < k → i ≠ j → (row_map h hh x)^[i] (H_val h hh x) ≠ (row_map h hh x)^[j] (H_val h hh x)) :
  N_active h hh x k ≤ (Finset.Icc (a_act h hh x).val (b_act h hh x).val).card :=
by
  rw [N_active_eq_card_filter h hh x k]
  apply Finset.card_le_card_of_injOn (f := fun i => (pred2c h hh ((row_map h hh x)^[i] (H_val h hh x))).val)
  · exact N_active_maps_to_Icc h hh x h_act k
  · intro i hi j hj heq
    exact N_active_inj_on_filter h hh x k h_distinct i hi j hj heq

theorem H_sub_J_eq_L_act_Z (h : ℕ) (hh : 5 ≤ h) (x : Fin (2 * h)) (h_act : ∃ y, activeB2 h x y) :
  H_sub_J h hh x = (L_act h hh x : ℤ) :=
by
  obtain ⟨y, hy⟩ := h_act
  unfold activeB2 at hy
  by_cases h_mod : h % 2 = 0
  · rw [if_pos h_mod] at hy
    rcases hy with ⟨hx, _⟩ | ⟨hx, _⟩
    · -- Case 1
      have hx_val : x.val = h + 1 := hx
      have hy2S : y2SwitchRow h x := by unfold y2SwitchRow; omega
      have h_y2star : y2star h hh x = ⟨2 * h - 2, by omega⟩ := by
        unfold y2star mMinusTwo2
        rw [if_pos hy2S, if_pos h_mod]
      have h_A2 : A2 h hh x = ⟨2 * h - 1, by omega⟩ := by
        unfold A2 succ2c one2
        rw [h_y2star]
        apply Fin.ext
        change (2 * h - 2 + 1) % (2 * h) = 2 * h - 1
        have : 2 * h - 2 + 1 = 2 * h - 1 := by omega
        rw [this]
        apply Nat.mod_eq_of_lt; omega
      have h_jump_y : jump_y h hh x = ⟨0, by omega⟩ := by
        unfold jump_y succ2c one2
        rw [h_A2]
        apply Fin.ext
        change (2 * h - 1 + 1) % (2 * h) = 0
        have : 2 * h - 1 + 1 = 2 * h := by omega
        rw [this]
        exact Nat.mod_self (2 * h)
      have h_pred_x : pred2c h hh x = ⟨h, by omega⟩ := by
        unfold pred2c one2
        apply Fin.ext
        change (2 * h - 1 + x.val) % (2 * h) = h
        rw [hx_val]
        have h1 : 2 * h - 1 + (h + 1) = h + 2 * h := by omega
        rw [h1, Nat.add_mod_right]
        apply Nat.mod_eq_of_lt; omega
      have h_cond : ¬ ((pred2c h hh x).val = h + 1 ∨ (pred2c h hh x).val = h + 2) := by
        rw [h_pred_x]; change ¬ (h = h + 1 ∨ h = h + 2); omega
      have hy2S_y : ¬ y2SwitchRow h (pred2c h hh x) := by
        unfold y2SwitchRow; rw [h_pred_x]; change ¬ (h = h + 1 ∨ h = h + 2 ∨ h = h + 3); omega
      have h_y2star_y : y2star h hh (pred2c h hh x) = ⟨h - 1, by omega⟩ := by
        unfold y2star
        rw [if_neg hy2S_y]
        apply Fin.ext
        change 2 * h - 1 - (pred2c h hh x).val = h - 1
        have hp_val : (pred2c h hh x).val = h := by rw [h_pred_x]
        rw [hp_val]
        omega
      have h_A2_y : A2 h hh (pred2c h hh x) = ⟨h, by omega⟩ := by
        unfold A2 succ2c one2
        rw [h_y2star_y]
        apply Fin.ext
        change (h - 1 + 1) % (2 * h) = h
        have : h - 1 + 1 = h := by omega
        rw [this]
        apply Nat.mod_eq_of_lt; omega
      have h_H_val : H_val h hh x = ⟨h - 1, by omega⟩ := by
        unfold H_val T_val
        rw [if_neg h_cond, h_A2_y]
        unfold pred2c one2
        apply Fin.ext
        change (2 * h - 1 + h) % (2 * h) = h - 1
        have h1 : 2 * h - 1 + h = h - 1 + 2 * h := by omega
        rw [h1, Nat.add_mod_right]
        apply Nat.mod_eq_of_lt; omega
      have h_L : L_act h hh x = h - 1 := by
        unfold L_act
        rw [if_pos hx_val, if_pos h_mod]
      unfold H_sub_J
      rw [h_jump_y, h_H_val, h_L]
      change (↑(h - 1) : ℤ) - (↑0 : ℤ) = ↑(h - 1)
      push_cast
      omega
    · -- Case 2
      have hx_val : x.val = h + 4 := hx
      have hy2S : ¬ y2SwitchRow h x := by unfold y2SwitchRow; omega
      have h_y2star : y2star h hh x = ⟨h - 5, by omega⟩ := by
        unfold y2star
        rw [if_neg hy2S]
        apply Fin.ext
        change 2 * h - 1 - x.val = h - 5
        rw [hx_val]
        omega
      have h_A2 : A2 h hh x = ⟨h - 4, by omega⟩ := by
        unfold A2 succ2c one2
        rw [h_y2star]
        apply Fin.ext
        change (h - 5 + 1) % (2 * h) = h - 4
        have : h - 5 + 1 = h - 4 := by omega
        rw [this]
        apply Nat.mod_eq_of_lt; omega
      have h_jump_y : jump_y h hh x = ⟨h - 3, by omega⟩ := by
        unfold jump_y succ2c one2
        rw [h_A2]
        apply Fin.ext
        change (h - 4 + 1) % (2 * h) = h - 3
        have : h - 4 + 1 = h - 3 := by omega
        rw [this]
        apply Nat.mod_eq_of_lt; omega
      have h_pred_x : pred2c h hh x = ⟨h + 3, by omega⟩ := by
        unfold pred2c one2
        apply Fin.ext
        change (2 * h - 1 + x.val) % (2 * h) = h + 3
        rw [hx_val]
        have h1 : 2 * h - 1 + (h + 4) = h + 3 + 2 * h := by omega
        rw [h1, Nat.add_mod_right]
        apply Nat.mod_eq_of_lt; omega
      have h_cond : ¬ ((pred2c h hh x).val = h + 1 ∨ (pred2c h hh x).val = h + 2) := by
        have hp_val : (pred2c h hh x).val = h + 3 := by rw [h_pred_x]
        rw [hp_val]; omega
      have hy2S_y : y2SwitchRow h (pred2c h hh x) := by
        unfold y2SwitchRow
        have hp_val : (pred2c h hh x).val = h + 3 := by rw [h_pred_x]
        rw [hp_val]; omega
      have h_y2star_y : y2star h hh (pred2c h hh x) = ⟨2 * h - 2, by omega⟩ := by
        unfold y2star mMinusTwo2
        rw [if_pos hy2S_y, if_pos h_mod]
      have h_A2_y : A2 h hh (pred2c h hh x) = ⟨2 * h - 1, by omega⟩ := by
        unfold A2 succ2c one2
        rw [h_y2star_y]
        apply Fin.ext
        change (2 * h - 2 + 1) % (2 * h) = 2 * h - 1
        have : 2 * h - 2 + 1 = 2 * h - 1 := by omega
        rw [this]
        apply Nat.mod_eq_of_lt; omega
      have h_H_val : H_val h hh x = ⟨2 * h - 2, by omega⟩ := by
        unfold H_val T_val
        rw [if_neg h_cond, h_A2_y]
        unfold pred2c one2
        apply Fin.ext
        change (2 * h - 1 + (2 * h - 1)) % (2 * h) = 2 * h - 2
        have h1 : 2 * h - 1 + (2 * h - 1) = 2 * h - 2 + 2 * h := by omega
        rw [h1, Nat.add_mod_right]
        apply Nat.mod_eq_of_lt; omega
      have hx_neq : ¬ (x.val = h + 1) := by omega
      have h_L : L_act h hh x = h + 1 := by
        unfold L_act
        rw [if_neg hx_neq, if_pos h_mod]
      unfold H_sub_J
      rw [h_jump_y, h_H_val, h_L]
      change (↑(2 * h - 2) : ℤ) - (↑(h - 3) : ℤ) = ↑(h + 1)
      push_cast
      omega
  · rw [if_neg h_mod] at hy
    rcases hy with ⟨hx, _⟩ | ⟨hx, _⟩
    · -- Case 3
      have hx_val : x.val = h + 1 := hx
      have hy2S : y2SwitchRow h x := by unfold y2SwitchRow; omega
      have h_y2star : y2star h hh x = ⟨2 * h - 1, by omega⟩ := by
        unfold y2star mMinusOne2
        rw [if_pos hy2S, if_neg h_mod]
      have h_A2 : A2 h hh x = ⟨0, by omega⟩ := by
        unfold A2 succ2c one2
        rw [h_y2star]
        apply Fin.ext
        change (2 * h - 1 + 1) % (2 * h) = 0
        have : 2 * h - 1 + 1 = 2 * h := by omega
        rw [this]
        exact Nat.mod_self (2 * h)
      have h_jump_y : jump_y h hh x = ⟨1, by omega⟩ := by
        unfold jump_y succ2c one2
        rw [h_A2]
        apply Fin.ext
        change (0 + 1) % (2 * h) = 1
        apply Nat.mod_eq_of_lt; omega
      have h_pred_x : pred2c h hh x = ⟨h, by omega⟩ := by
        unfold pred2c one2
        apply Fin.ext
        change (2 * h - 1 + x.val) % (2 * h) = h
        rw [hx_val]
        have h1 : 2 * h - 1 + (h + 1) = h + 2 * h := by omega
        rw [h1, Nat.add_mod_right]
        apply Nat.mod_eq_of_lt; omega
      have h_cond : ¬ ((pred2c h hh x).val = h + 1 ∨ (pred2c h hh x).val = h + 2) := by
        have hp_val : (pred2c h hh x).val = h := by rw [h_pred_x]
        rw [hp_val]; omega
      have hy2S_y : ¬ y2SwitchRow h (pred2c h hh x) := by
        unfold y2SwitchRow
        have hp_val : (pred2c h hh x).val = h := by rw [h_pred_x]
        rw [hp_val]; omega
      have h_y2star_y : y2star h hh (pred2c h hh x) = ⟨h - 1, by omega⟩ := by
        unfold y2star
        rw [if_neg hy2S_y]
        apply Fin.ext
        change 2 * h - 1 - (pred2c h hh x).val = h - 1
        have hp_val : (pred2c h hh x).val = h := by rw [h_pred_x]
        rw [hp_val]
        omega
      have h_A2_y : A2 h hh (pred2c h hh x) = ⟨h, by omega⟩ := by
        unfold A2 succ2c one2
        rw [h_y2star_y]
        apply Fin.ext
        change (h - 1 + 1) % (2 * h) = h
        have : h - 1 + 1 = h := by omega
        rw [this]
        apply Nat.mod_eq_of_lt; omega
      have h_H_val : H_val h hh x = ⟨h - 1, by omega⟩ := by
        unfold H_val T_val
        rw [if_neg h_cond, h_A2_y]
        unfold pred2c one2
        apply Fin.ext
        change (2 * h - 1 + h) % (2 * h) = h - 1
        have h1 : 2 * h - 1 + h = h - 1 + 2 * h := by omega
        rw [h1, Nat.add_mod_right]
        apply Nat.mod_eq_of_lt; omega
      have h_L : L_act h hh x = h - 2 := by
        unfold L_act
        rw [if_pos hx_val, if_neg h_mod]
      unfold H_sub_J
      rw [h_jump_y, h_H_val, h_L]
      change (↑(h - 1) : ℤ) - (↑1 : ℤ) = ↑(h - 2)
      push_cast
      omega
    · -- Case 4
      have hx_val : x.val = h + 4 := hx
      have hy2S : ¬ y2SwitchRow h x := by unfold y2SwitchRow; omega
      have h_y2star : y2star h hh x = ⟨h - 5, by omega⟩ := by
        unfold y2star
        rw [if_neg hy2S]
        apply Fin.ext
        change 2 * h - 1 - x.val = h - 5
        rw [hx_val]
        omega
      have h_A2 : A2 h hh x = ⟨h - 4, by omega⟩ := by
        unfold A2 succ2c one2
        rw [h_y2star]
        apply Fin.ext
        change (h - 5 + 1) % (2 * h) = h - 4
        have : h - 5 + 1 = h - 4 := by omega
        rw [this]
        apply Nat.mod_eq_of_lt; omega
      have h_jump_y : jump_y h hh x = ⟨h - 3, by omega⟩ := by
        unfold jump_y succ2c one2
        rw [h_A2]
        apply Fin.ext
        change (h - 4 + 1) % (2 * h) = h - 3
        have : h - 4 + 1 = h - 3 := by omega
        rw [this]
        apply Nat.mod_eq_of_lt; omega
      have h_pred_x : pred2c h hh x = ⟨h + 3, by omega⟩ := by
        unfold pred2c one2
        apply Fin.ext
        change (2 * h - 1 + x.val) % (2 * h) = h + 3
        rw [hx_val]
        have h1 : 2 * h - 1 + (h + 4) = h + 3 + 2 * h := by omega
        rw [h1, Nat.add_mod_right]
        apply Nat.mod_eq_of_lt; omega
      have h_cond : ¬ ((pred2c h hh x).val = h + 1 ∨ (pred2c h hh x).val = h + 2) := by
        have hp_val : (pred2c h hh x).val = h + 3 := by rw [h_pred_x]
        rw [hp_val]; omega
      have hy2S_y : y2SwitchRow h (pred2c h hh x) := by
        unfold y2SwitchRow
        have hp_val : (pred2c h hh x).val = h + 3 := by rw [h_pred_x]
        rw [hp_val]; omega
      have h_y2star_y : y2star h hh (pred2c h hh x) = ⟨2 * h - 1, by omega⟩ := by
        unfold y2star mMinusOne2
        rw [if_pos hy2S_y, if_neg h_mod]
      have h_A2_y : A2 h hh (pred2c h hh x) = ⟨0, by omega⟩ := by
        unfold A2 succ2c one2
        rw [h_y2star_y]
        apply Fin.ext
        change (2 * h - 1 + 1) % (2 * h) = 0
        have : 2 * h - 1 + 1 = 2 * h := by omega
        rw [this]
        exact Nat.mod_self (2 * h)
      have h_H_val : H_val h hh x = ⟨2 * h - 1, by omega⟩ := by
        unfold H_val T_val
        rw [if_neg h_cond, h_A2_y]
        unfold pred2c one2
        apply Fin.ext
        change (2 * h - 1 + 0) % (2 * h) = 2 * h - 1
        have h1 : 2 * h - 1 + 0 = 2 * h - 1 := by omega
        rw [h1]
        apply Nat.mod_eq_of_lt; omega
      have hx_neq : ¬ (x.val = h + 1) := by omega
      have h_L : L_act h hh x = h + 2 := by
        unfold L_act
        rw [if_neg hx_neq, if_neg h_mod]
      unfold H_sub_J
      rw [h_jump_y, h_H_val, h_L]
      change (↑(2 * h - 1) : ℤ) - (↑(h - 3) : ℤ) = ↑(h + 2)
      push_cast
      omega

theorem N_active_bound (h : ℕ) (hh : 5 ≤ h) (x : Fin (2 * h)) (h_act : ∃ y, activeB2 h x y) (k : ℕ)
  (h_distinct : ∀ i j, i < k → j < k → i ≠ j → (row_map h hh x)^[i] (H_val h hh x) ≠ (row_map h hh x)^[j] (H_val h hh x)) :
  (N_active h hh x k : ℤ) ≤ H_sub_J h hh x + 1 :=
by
  have h1 := N_active_le_Icc_card h hh x h_act k h_distinct
  have h2 := active_Icc_card_eq h hh x h_act
  have h3 := H_sub_J_eq_L_act_Z h hh x h_act
  omega

theorem total_desc_bound_min (h : ℕ) (hh : 5 ≤ h) (x : Fin (2 * h)) (h_act : ∃ y, activeB2 h x y) (k : ℕ)
  (hk_jump : (row_map h hh x)^[k] (H_val h hh x) = jump_y h hh x)
  (hk_min : ∀ j < k, (row_map h hh x)^[j] (H_val h hh x) ≠ jump_y h hh x) :
  (total_desc h hh x k : ℤ) ≤ (k : ℤ) + H_sub_J h hh x + 1 :=
by
  have hd : ∀ i j, i < k → j < k → i ≠ j → (row_map h hh x)^[i] (H_val h hh x) ≠ (row_map h hh x)^[j] (H_val h hh x) :=
    trajectory_distinct_of_min_jump h hh x k hk_jump hk_min
  have h_eq : (total_desc h hh x k : ℤ) = (k : ℤ) + (N_active h hh x k : ℤ) :=
    total_desc_eq_k_plus_N_active_Z h hh x k
  have h_bound : (N_active h hh x k : ℤ) ≤ H_sub_J h hh x + 1 :=
    N_active_bound h hh x h_act k hd
  linarith

theorem two_mul_mod_two (k : ℕ) : (2 * k) % 2 = 0 :=
by
  omega

theorem total_desc_eq_L_act (h : ℕ) (hh : 5 ≤ h) (x : Fin (2 * h)) (k : ℕ)
  (h_act : ∃ y, activeB2 h x y)
  (hc0 : (total_desc h hh x k : ℤ) = H_sub_J h hh x) :
  total_desc h hh x k = L_act h hh x :=
by
  have h_pred_val : ∀ (y : Fin (2 * h)), y.val > 0 → (pred2c h hh y).val = y.val - 1 := by
    intro y hy
    unfold pred2c one2
    change (2 * h - 1 + y.val) % (2 * h) = y.val - 1
    have h1 : 2 * h - 1 + y.val = (y.val - 1) + 2 * h := by omega
    rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

  have h_pred_zero : ∀ (y : Fin (2 * h)), y.val = 0 → (pred2c h hh y).val = 2 * h - 1 := by
    intro y hy
    unfold pred2c one2
    change (2 * h - 1 + y.val) % (2 * h) = 2 * h - 1
    rw [hy]
    have h1 : 2 * h - 1 + 0 = 2 * h - 1 := by omega
    rw [h1]
    exact Nat.mod_eq_of_lt (by omega)

  have h_succ_val : ∀ (y : Fin (2 * h)), y.val + 1 < 2 * h → (succ2c h hh y).val = y.val + 1 := by
    intro y hy
    unfold succ2c one2
    change (y.val + 1) % (2 * h) = y.val + 1
    exact Nat.mod_eq_of_lt hy

  have h_succ_wrap : ∀ (y : Fin (2 * h)), y.val + 1 = 2 * h → (succ2c h hh y).val = 0 := by
    intro y hy
    unfold succ2c one2
    change (y.val + 1) % (2 * h) = 0
    rw [hy, Nat.mod_self]

  by_cases heven : h % 2 = 0
  · have hx : x.val = h + 1 ∨ x.val = h + 4 := by
      rcases h_act with ⟨y, hy⟩
      unfold activeB2 at hy
      rw [if_pos heven] at hy
      rcases hy with ⟨hx1, _⟩ | ⟨hx4, _⟩
      · left; exact hx1
      · right; exact hx4
    rcases hx with hx1 | hx4
    · -- Case 1: h % 2 = 0, x.val = h + 1
      have hp : (pred2c h hh x).val = h := by
        have h_gt : x.val > 0 := by omega
        rw [h_pred_val x h_gt]
        omega
      have hy2star : (y2star h hh (pred2c h hh x)).val = h - 1 := by
        unfold y2star
        have h_switch : ¬ y2SwitchRow h (pred2c h hh x) := by
          unfold y2SwitchRow; rw [hp]; omega
        rw [if_neg h_switch]
        change 2 * h - 1 - (pred2c h hh x).val = h - 1
        rw [hp]
        omega
      have hA2 : (A2 h hh (pred2c h hh x)).val = h := by
        unfold A2
        have h_lt : (y2star h hh (pred2c h hh x)).val + 1 < 2 * h := by rw [hy2star]; omega
        rw [h_succ_val _ h_lt]
        rw [hy2star]
        omega
      have hT : (H_val h hh x).val = h - 1 := by
        unfold H_val T_val
        have h_cond : ¬((pred2c h hh x).val = h + 1 ∨ (pred2c h hh x).val = h + 2) := by rw [hp]; omega
        rw [if_neg h_cond]
        have h_gt : (A2 h hh (pred2c h hh x)).val > 0 := by rw [hA2]; omega
        rw [h_pred_val _ h_gt]
        rw [hA2]
      have hy2star_x : (y2star h hh x).val = 2 * h - 2 := by
        unfold y2star
        have h_switch : y2SwitchRow h x := by
          unfold y2SwitchRow; omega
        rw [if_pos h_switch, if_pos heven]
        rfl
      have hA2_x : (A2 h hh x).val = 2 * h - 1 := by
        unfold A2
        have h_lt : (y2star h hh x).val + 1 < 2 * h := by rw [hy2star_x]; omega
        rw [h_succ_val _ h_lt]
        rw [hy2star_x]
        omega
      have hjump_y : (jump_y h hh x).val = 0 := by
        unfold jump_y
        have h_eq : (A2 h hh x).val + 1 = 2 * h := by rw [hA2_x]; omega
        rw [h_succ_wrap _ h_eq]
      have hH_sub_J : H_sub_J h hh x = (h - 1 : ℤ) := by
        unfold H_sub_J
        rw [hT, hjump_y]
        push_cast
        omega
      have hL_act : L_act h hh x = h - 1 := by
        unfold L_act
        change (if x.val = h + 1 then if h % 2 = 0 then h - 1 else h - 2 else if h % 2 = 0 then h + 1 else h + 2) = h - 1
        rw [if_pos hx1, if_pos heven]
      omega

    · -- Case 2: h % 2 = 0, x.val = h + 4
      have hp : (pred2c h hh x).val = h + 3 := by
        have h_gt : x.val > 0 := by omega
        rw [h_pred_val x h_gt]
        omega
      have hy2star : (y2star h hh (pred2c h hh x)).val = 2 * h - 2 := by
        unfold y2star
        have h_switch : y2SwitchRow h (pred2c h hh x) := by
          unfold y2SwitchRow; rw [hp]; omega
        rw [if_pos h_switch, if_pos heven]
        rfl
      have hA2 : (A2 h hh (pred2c h hh x)).val = 2 * h - 1 := by
        unfold A2
        have h_lt : (y2star h hh (pred2c h hh x)).val + 1 < 2 * h := by rw [hy2star]; omega
        rw [h_succ_val _ h_lt]
        rw [hy2star]
        omega
      have hT : (H_val h hh x).val = 2 * h - 2 := by
        unfold H_val T_val
        have h_cond : ¬((pred2c h hh x).val = h + 1 ∨ (pred2c h hh x).val = h + 2) := by rw [hp]; omega
        rw [if_neg h_cond]
        have h_gt : (A2 h hh (pred2c h hh x)).val > 0 := by rw [hA2]; omega
        rw [h_pred_val _ h_gt]
        rw [hA2]
        omega
      have hy2star_x : (y2star h hh x).val = h - 5 := by
        unfold y2star
        have h_switch : ¬ y2SwitchRow h x := by
          unfold y2SwitchRow; omega
        rw [if_neg h_switch]
        change 2 * h - 1 - x.val = h - 5
        omega
      have hA2_x : (A2 h hh x).val = h - 4 := by
        unfold A2
        have h_lt : (y2star h hh x).val + 1 < 2 * h := by rw [hy2star_x]; omega
        rw [h_succ_val _ h_lt]
        rw [hy2star_x]
        omega
      have hjump_y : (jump_y h hh x).val = h - 3 := by
        unfold jump_y
        have h_lt : (A2 h hh x).val + 1 < 2 * h := by rw [hA2_x]; omega
        rw [h_succ_val _ h_lt]
        rw [hA2_x]
        omega
      have hH_sub_J : H_sub_J h hh x = (h + 1 : ℤ) := by
        unfold H_sub_J
        rw [hT, hjump_y]
        push_cast
        omega
      have hL_act : L_act h hh x = h + 1 := by
        unfold L_act
        change (if x.val = h + 1 then if h % 2 = 0 then h - 1 else h - 2 else if h % 2 = 0 then h + 1 else h + 2) = h + 1
        have hx1_false : ¬(x.val = h + 1) := by omega
        rw [if_neg hx1_false, if_pos heven]
      omega

  · have hodd : ¬(h % 2 = 0) := heven
    have hx : x.val = h + 1 ∨ x.val = h + 4 := by
      rcases h_act with ⟨y, hy⟩
      unfold activeB2 at hy
      rw [if_neg hodd] at hy
      rcases hy with ⟨hx1, _⟩ | ⟨hx4, _⟩
      · left; exact hx1
      · right; exact hx4
    rcases hx with hx1 | hx4
    · -- Case 3: h % 2 ≠ 0, x.val = h + 1
      have hp : (pred2c h hh x).val = h := by
        have h_gt : x.val > 0 := by omega
        rw [h_pred_val x h_gt]
        omega
      have hy2star : (y2star h hh (pred2c h hh x)).val = h - 1 := by
        unfold y2star
        have h_switch : ¬ y2SwitchRow h (pred2c h hh x) := by
          unfold y2SwitchRow; rw [hp]; omega
        rw [if_neg h_switch]
        change 2 * h - 1 - (pred2c h hh x).val = h - 1
        rw [hp]
        omega
      have hA2 : (A2 h hh (pred2c h hh x)).val = h := by
        unfold A2
        have h_lt : (y2star h hh (pred2c h hh x)).val + 1 < 2 * h := by rw [hy2star]; omega
        rw [h_succ_val _ h_lt]
        rw [hy2star]
        omega
      have hT : (H_val h hh x).val = h - 1 := by
        unfold H_val T_val
        have h_cond : ¬((pred2c h hh x).val = h + 1 ∨ (pred2c h hh x).val = h + 2) := by rw [hp]; omega
        rw [if_neg h_cond]
        have h_gt : (A2 h hh (pred2c h hh x)).val > 0 := by rw [hA2]; omega
        rw [h_pred_val _ h_gt]
        rw [hA2]
      have hy2star_x : (y2star h hh x).val = 2 * h - 1 := by
        unfold y2star
        have h_switch : y2SwitchRow h x := by
          unfold y2SwitchRow; omega
        rw [if_pos h_switch, if_neg hodd]
        rfl
      have hA2_x : (A2 h hh x).val = 0 := by
        unfold A2
        have h_eq : (y2star h hh x).val + 1 = 2 * h := by rw [hy2star_x]; omega
        rw [h_succ_wrap _ h_eq]
      have hjump_y : (jump_y h hh x).val = 1 := by
        unfold jump_y
        have h_lt : (A2 h hh x).val + 1 < 2 * h := by rw [hA2_x]; omega
        rw [h_succ_val _ h_lt]
        rw [hA2_x]
      have hH_sub_J : H_sub_J h hh x = (h - 2 : ℤ) := by
        unfold H_sub_J
        rw [hT, hjump_y]
        push_cast
        omega
      have hL_act : L_act h hh x = h - 2 := by
        unfold L_act
        change (if x.val = h + 1 then if h % 2 = 0 then h - 1 else h - 2 else if h % 2 = 0 then h + 1 else h + 2) = h - 2
        rw [if_pos hx1, if_neg hodd]
      omega

    · -- Case 4: h % 2 ≠ 0, x.val = h + 4
      have hp : (pred2c h hh x).val = h + 3 := by
        have h_gt : x.val > 0 := by omega
        rw [h_pred_val x h_gt]
        omega
      have hy2star : (y2star h hh (pred2c h hh x)).val = 2 * h - 1 := by
        unfold y2star
        have h_switch : y2SwitchRow h (pred2c h hh x) := by
          unfold y2SwitchRow; rw [hp]; omega
        rw [if_pos h_switch, if_neg hodd]
        rfl
      have hA2 : (A2 h hh (pred2c h hh x)).val = 0 := by
        unfold A2
        have h_eq : (y2star h hh (pred2c h hh x)).val + 1 = 2 * h := by rw [hy2star]; omega
        rw [h_succ_wrap _ h_eq]
      have hT : (H_val h hh x).val = 2 * h - 1 := by
        unfold H_val T_val
        have h_cond : ¬((pred2c h hh x).val = h + 1 ∨ (pred2c h hh x).val = h + 2) := by rw [hp]; omega
        rw [if_neg h_cond]
        have h_eq : (A2 h hh (pred2c h hh x)).val = 0 := hA2
        rw [h_pred_zero _ h_eq]
      have hy2star_x : (y2star h hh x).val = h - 5 := by
        unfold y2star
        have h_switch : ¬ y2SwitchRow h x := by
          unfold y2SwitchRow; omega
        rw [if_neg h_switch]
        change 2 * h - 1 - x.val = h - 5
        omega
      have hA2_x : (A2 h hh x).val = h - 4 := by
        unfold A2
        have h_lt : (y2star h hh x).val + 1 < 2 * h := by rw [hy2star_x]; omega
        rw [h_succ_val _ h_lt]
        rw [hy2star_x]
        omega
      have hjump_y : (jump_y h hh x).val = h - 3 := by
        unfold jump_y
        have h_lt : (A2 h hh x).val + 1 < 2 * h := by rw [hA2_x]; omega
        rw [h_succ_val _ h_lt]
        rw [hA2_x]
        omega
      have hH_sub_J : H_sub_J h hh x = (h + 2 : ℤ) := by
        unfold H_sub_J
        rw [hT, hjump_y]
        push_cast
        omega
      have hL_act : L_act h hh x = h + 2 := by
        unfold L_act
        change (if x.val = h + 1 then if h % 2 = 0 then h - 1 else h - 2 else if h % 2 = 0 then h + 1 else h + 2) = h + 2
        have hx1_false : ¬(x.val = h + 1) := by omega
        rw [if_neg hx1_false, if_neg hodd]
      omega

theorem step_desc_val_eq_two (h : ℕ) (hh : 5 ≤ h) (x y : Fin (2 * h))
  (h_act : activeB2 h x (pred2c h hh y)) :
  step_desc h hh x y = 2 :=
by
  unfold step_desc
  split
  · rfl
  · contradiction

theorem activeB2_iff_in_interval (h : ℕ) (hh : 5 ≤ h) (x y : Fin (2 * h))
  (h_act : ∃ u, activeB2 h x u) :
  activeB2 h x y ↔ (a_act h hh x).val ≤ y.val ∧ y.val ≤ (b_act h hh x).val :=
by
  obtain ⟨u, hu⟩ := h_act
  unfold activeB2 a_act b_act at *
  by_cases h_even : h % 2 = 0
  · by_cases hx : x.val = h + 1
    · simp [h_even, hx] at hu ⊢
    · simp [h_even, hx] at hu ⊢
      omega
  · by_cases hx : x.val = h + 1
    · simp [h_even, hx] at hu ⊢
    · simp [h_even, hx] at hu ⊢
      omega

theorem H_val_eq_b_act (x : Fin (2 * h)) (h_act : ∃ y, activeB2 h x y) :
  H_val h hh x = b_act h hh x :=
by
  rcases h_act with ⟨y, hy⟩
  dsimp [activeB2] at hy
  have hx : x.val = h + 1 ∨ x.val = h + 4 := by
    split_ifs at hy
    · rcases hy with ⟨h1, _⟩ | ⟨h4, _⟩
      · exact Or.inl h1
      · exact Or.inr h4
    · rcases hy with ⟨h1, _⟩ | ⟨h4, _⟩
      · exact Or.inl h1
      · exact Or.inr h4

  have h_pred_val : ∀ (v : ℕ), x.val = v → 1 ≤ v → v < 2 * h → (pred2c h hh x).val = v - 1 := by
    intro v hx_val hv1 hv_lt
    change (2 * h - 1 + x.val) % (2 * h) = v - 1
    rw [hx_val]
    have : 2 * h - 1 + v = v - 1 + 2 * h := by omega
    rw [this, Nat.add_mod_right]
    exact Nat.mod_eq_of_lt (by omega)

  have h_cancel : ∀ z, pred2c h hh (succ2c h hh z) = z := by
    intro z
    ext
    change (2 * h - 1 + (z.val + 1) % (2 * h)) % (2 * h) = z.val
    have h_z_lt : z.val < 2 * h := z.isLt
    have h_cases : z.val + 1 = 2 * h ∨ z.val + 1 < 2 * h := by omega
    rcases h_cases with heq | hlt
    · rw [heq]
      have h1 : (2 * h) % (2 * h) = 0 := Nat.mod_self (2 * h)
      rw [h1]
      have h2 : (2 * h - 1 + 0) % (2 * h) = 2 * h - 1 := by
        apply Nat.mod_eq_of_lt
        omega
      rw [h2]
      omega
    · have h1 : (z.val + 1) % (2 * h) = z.val + 1 := by
        apply Nat.mod_eq_of_lt
        exact hlt
      rw [h1]
      have h2 : 2 * h - 1 + (z.val + 1) = z.val + 2 * h := by omega
      rw [h2, Nat.add_mod_right]
      exact Nat.mod_eq_of_lt h_z_lt

  unfold H_val T_val
  rcases hx with h1 | h4
  · have h_p : (pred2c h hh x).val = h := by
      have h_lt : h + 1 < 2 * h := by omega
      have hpv := h_pred_val (h + 1) h1 (by omega) h_lt
      have heq : h + 1 - 1 = h := by omega
      rw [heq] at hpv
      exact hpv
    have h_not : ¬ ((pred2c h hh x).val = h + 1 ∨ (pred2c h hh x).val = h + 2) := by omega
    rw [if_neg h_not]
    unfold A2
    rw [h_cancel]
    unfold y2star
    have h_switch : ¬ y2SwitchRow h (pred2c h hh x) := by
      unfold y2SwitchRow
      omega
    rw [if_neg h_switch]

    ext
    unfold b_act
    rw [if_pos h1]
    change 2 * h - 1 - (pred2c h hh x).val = h - 1
    omega

  · have h_p : (pred2c h hh x).val = h + 3 := by
      have h_lt : h + 4 < 2 * h := by omega
      have hpv := h_pred_val (h + 4) h4 (by omega) h_lt
      have heq : h + 4 - 1 = h + 3 := by omega
      rw [heq] at hpv
      exact hpv
    have h_not : ¬ ((pred2c h hh x).val = h + 1 ∨ (pred2c h hh x).val = h + 2) := by omega
    rw [if_neg h_not]
    unfold A2
    rw [h_cancel]
    unfold y2star
    have h_switch : y2SwitchRow h (pred2c h hh x) := by
      unfold y2SwitchRow
      omega
    rw [if_pos h_switch]

    ext
    unfold b_act mMinusTwo2 mMinusOne2
    have h_x_neq : x.val ≠ h + 1 := by omega
    rw [if_neg h_x_neq]

theorem a_b_L_act_props (x : Fin (2 * h)) (h_act : ∃ y, activeB2 h x y) :
  (b_act h hh x).val = (a_act h hh x).val + L_act h hh x ∧
  L_act h hh x = 2 * k_track2 h hh x + 1 ∧
  (b_act h hh x).val ≥ L_act h hh x ∧
  L_act h hh x ≥ 3 :=
by
  rcases h_act with ⟨y, hy⟩
  unfold activeB2 at hy
  by_cases h_mod : h % 2 = 0
  · simp only [h_mod, if_true] at hy
    rcases hy with ⟨hx, _⟩ | ⟨hx, _, _⟩
    · simp only [k_track2, L_act, a_act, b_act]
      simp [hx, h_mod]
      omega
    · simp only [k_track2, L_act, a_act, b_act]
      have hx_not : ¬(x.val = h + 1) := by omega
      simp [hx_not, h_mod]
      omega
  · simp only [h_mod, if_false] at hy
    have h_odd : h % 2 = 1 := by omega
    rcases hy with ⟨hx, _, _⟩ | ⟨hx, _⟩
    · simp only [k_track2, L_act, a_act, b_act]
      simp [hx, h_mod]
      omega
    · simp only [k_track2, L_act, a_act, b_act]
      have hx_not : ¬(x.val = h + 1) := by omega
      simp [hx_not, h_mod]
      omega

theorem iterate_succ_out {α : Type} (f : α → α) (n : ℕ) (a : α) :
  f^[n + 1] a = f (f^[n] a) :=
by
  exact Function.iterate_succ_apply' f n a

theorem total_desc_le_succ (h : ℕ) (hh : 5 ≤ h) (x : Fin (2 * h)) (k : ℕ) :
  total_desc h hh x k ≤ total_desc h hh x (k + 1) :=
by
  have H : total_desc h hh x (k + 1) = total_desc h hh x k + step_desc h hh x ((row_map h hh x)^[k] (H_val h hh x)) := rfl
  rw [H]
  omega

theorem total_desc_mono (h : ℕ) (hh : 5 ≤ h) (x : Fin (2 * h)) {j k : ℕ} (hjk : j ≤ k) :
  total_desc h hh x j ≤ total_desc h hh x k :=
by
  induction hjk with
  | refl => exact Nat.le_refl _
  | step _ ih => exact Nat.le_trans ih (total_desc_le_succ h hh x _)

theorem row_map_val_add_step_desc (h : ℕ) (hh : 5 ≤ h) (x y : Fin (2 * h))
  (h_not_jump : y ≠ jump_y h hh x)
  (h_bound : step_desc h hh x y ≤ y.val) :
  (row_map h hh x y).val + step_desc h hh x y = y.val :=
by
  have h_pred : ∀ (z : Fin (2 * h)), 1 ≤ z.val → (pred2c h hh z).val = z.val - 1 := by
    intro z hz
    haveI : NeZero (2 * h) := ⟨by omega⟩
    have h_eq : pred2c h hh z + one2 h hh = z := by
      unfold pred2c
      exact sub_add_cancel z (one2 h hh)
    have h_val : (pred2c h hh z + one2 h hh).val = z.val := by rw [h_eq]
    have h_add : (pred2c h hh z + one2 h hh).val = ((pred2c h hh z).val + 1) % (2 * h) := rfl
    rw [h_add] at h_val
    have h_lt : (pred2c h hh z).val < 2 * h := (pred2c h hh z).isLt
    have h_cases : (pred2c h hh z).val + 1 < 2 * h ∨ (pred2c h hh z).val + 1 = 2 * h := by omega
    cases h_cases with
    | inl h_lt2 =>
      have h_mod := Nat.mod_eq_of_lt h_lt2
      rw [h_mod] at h_val
      omega
    | inr h_eq2 =>
      have h_mod : (2 * h) % (2 * h) = 0 := Nat.mod_self (2 * h)
      rw [h_eq2] at h_val
      rw [h_mod] at h_val
      omega
  unfold step_desc at h_bound ⊢
  unfold row_map
  by_cases h_act : activeB2 h x (pred2c h hh y)
  · simp only [if_neg h_not_jump, if_pos h_act] at h_bound ⊢
    have eq1 : (pred2c h hh y).val = y.val - 1 := h_pred y (by omega)
    have eq2 : (pred2c h hh (pred2c h hh y)).val = (pred2c h hh y).val - 1 := by
      apply h_pred
      omega
    rw [eq2, eq1]
    omega
  · simp only [if_neg h_not_jump, if_neg h_act] at h_bound ⊢
    have eq1 : (pred2c h hh y).val = y.val - 1 := h_pred y (by omega)
    rw [eq1]
    omega

theorem iterate_val_add_total_desc (h : ℕ) (hh : 5 ≤ h) (x : Fin (2 * h)) (k : ℕ)
  (h_act : ∃ y, activeB2 h x y)
  (h_total : total_desc h hh x k = L_act h hh x)
  (h_not_jump : ∀ j < k, (row_map h hh x)^[j] (H_val h hh x) ≠ jump_y h hh x) :
  ∀ j, j ≤ k → ((row_map h hh x)^[j] (H_val h hh x)).val + total_desc h hh x j = (b_act h hh x).val :=
by
  intro j
  induction j with
  | zero =>
    intro _
    have h_iter0 : (row_map h hh x)^[0] (H_val h hh x) = H_val h hh x := rfl
    have h_td0 : total_desc h hh x 0 = 0 := rfl
    rw [h_iter0, h_td0, H_val_eq_b_act h hh x h_act]
    omega
  | succ j ih =>
    intro hj1_le
    have hj_le : j ≤ k := by omega
    have hj_lt : j < k := by omega
    have ih_j := ih hj_le
    have h_iter : (row_map h hh x)^[j + 1] (H_val h hh x) = row_map h hh x ((row_map h hh x)^[j] (H_val h hh x)) :=
      iterate_succ_out (row_map h hh x) j (H_val h hh x)
    have h_td_eq : total_desc h hh x (j + 1) = total_desc h hh x j + step_desc h hh x ((row_map h hh x)^[j] (H_val h hh x)) := rfl
    have h_not_jump_j := h_not_jump j hj_lt
    have h_b_act_ge := (a_b_L_act_props h hh x h_act).2.2.1
    have h_td_mono : total_desc h hh x (j + 1) ≤ total_desc h hh x k := total_desc_mono h hh x hj1_le
    rw [h_total] at h_td_mono
    have h_bound : step_desc h hh x ((row_map h hh x)^[j] (H_val h hh x)) ≤ ((row_map h hh x)^[j] (H_val h hh x)).val := by
      omega
    have h_step := row_map_val_add_step_desc h hh x ((row_map h hh x)^[j] (H_val h hh x)) h_not_jump_j h_bound
    rw [h_iter, h_td_eq]
    omega

theorem pred2c_val_add_one (y : Fin (2 * h)) (hy : y.val ≥ 1) :
  (pred2c h hh y).val + 1 = y.val :=
by
  have eq1 := Fin.intCast_val_sub_eq_sub_add_ite y (one2 h hh)
  have h_le : one2 h hh ≤ y := by
    rw [← Fin.val_fin_le]
    change 1 ≤ y.val
    exact hy
  simp [h_le] at eq1
  have h_one : (one2 h hh).val = 1 := rfl
  unfold pred2c
  omega

theorem step_desc_pos (h : ℕ) (hh : 5 ≤ h) (x y : Fin (2 * h)) :
  1 ≤ step_desc h hh x y :=
by
  unfold step_desc
  split <;> omega

theorem total_desc_succ (h : ℕ) (hh : 5 ≤ h) (x : Fin (2 * h)) (k : ℕ) :
  total_desc h hh x k < total_desc h hh x (k + 1) :=
by
  have H := step_desc_pos h hh x ((row_map h hh x)^[k] (H_val h hh x))
  change total_desc h hh x k < total_desc h hh x k + step_desc h hh x ((row_map h hh x)^[k] (H_val h hh x))
  omega

theorem total_desc_strict_mono (h : ℕ) (hh : 5 ≤ h) (x : Fin (2 * h)) (j k : ℕ) (hjk : j < k) :
  total_desc h hh x j < total_desc h hh x k :=
strictMono_nat_of_lt_succ (total_desc_succ h hh x) hjk

theorem step_desc_is_two (h : ℕ) (hh : 5 ≤ h) (x : Fin (2 * h)) (k : ℕ)
  (h_act : ∃ y, activeB2 h x y)
  (h_total : total_desc h hh x k = L_act h hh x)
  (h_not_jump : ∀ j < k, (row_map h hh x)^[j] (H_val h hh x) ≠ jump_y h hh x) :
  ∀ j < k, step_desc h hh x ((row_map h hh x)^[j] (H_val h hh x)) = 2 :=
by
  intro j hj
  apply step_desc_val_eq_two
  apply (activeB2_iff_in_interval h hh x _ h_act).mpr
  have H1 := iterate_val_add_total_desc h hh x k h_act h_total h_not_jump j (Nat.le_of_lt hj)
  have H2_1 := (a_b_L_act_props h hh x h_act).1
  have H3 := total_desc_strict_mono h hh x j k hj
  have h_y_ge_1 : ((row_map h hh x)^[j] (H_val h hh x)).val ≥ 1 := by omega
  have h_pred := pred2c_val_add_one h hh ((row_map h hh x)^[j] (H_val h hh x)) h_y_ge_1
  constructor
  · omega
  · omega

theorem total_desc_eq_two_mul_k (h : ℕ) (hh : 5 ≤ h) (x : Fin (2 * h)) (k : ℕ)
  (h_step : ∀ j < k, step_desc h hh x ((row_map h hh x)^[j] (H_val h hh x)) = 2) :
  total_desc h hh x k = 2 * k :=
by
  induction k with
  | zero => rfl
  | succ n ih =>
    have hn : total_desc h hh x n = 2 * n := by
      apply ih
      intro j hj
      apply h_step
      omega
    have hn2 : step_desc h hh x ((row_map h hh x)^[n] (H_val h hh x)) = 2 := by
      apply h_step
      omega
    change total_desc h hh x n + step_desc h hh x ((row_map h hh x)^[n] (H_val h hh x)) = 2 * (n + 1)
    rw [hn, hn2]
    omega

theorem L_act_bounds (x : Fin (2 * h)) :
  3 ≤ L_act h hh x ∧ L_act h hh x ≤ 2 * h - 3 ∧ (L_act h hh x) % 2 = 1 :=
by
  have H : L_act h hh x = if x.val = h + 1 then
                            if h % 2 = 0 then h - 1 else h - 2
                          else
                            if h % 2 = 0 then h + 1 else h + 2 := rfl
  rw [H]
  split_ifs <;> omega

theorem c_eq_zero_impossible (h : ℕ) (hh : 5 ≤ h) (x : Fin (2 * h)) (h_act : ∃ y, activeB2 h x y) (k : ℕ)
  (hk_jump : (row_map h hh x)^[k] (H_val h hh x) = jump_y h hh x)
  (hk_min : ∀ j < k, (row_map h hh x)^[j] (H_val h hh x) ≠ jump_y h hh x)
  (hc0 : (total_desc h hh x k : ℤ) = H_sub_J h hh x) :
  False :=
by
  have h_tot : total_desc h hh x k = L_act h hh x := total_desc_eq_L_act h hh x k h_act hc0
  have h_steps : ∀ j < k, step_desc h hh x ((row_map h hh x)^[j] (H_val h hh x)) = 2 := step_desc_is_two h hh x k h_act h_tot hk_min
  have h_desc : total_desc h hh x k = 2 * k := total_desc_eq_two_mul_k h hh x k h_steps
  have h_L := L_act_bounds h hh x
  have h_mod := two_mul_mod_two k
  have H : 2 * k = L_act h hh x := by
    rw [← h_desc]
    exact h_tot
  have eq_mod : (L_act h hh x) % 2 = 1 := h_L.2.2
  rw [← H] at eq_mod
  rw [h_mod] at eq_mod
  omega

theorem row_map_active_not_jump (x : Fin (2 * h)) (h_act : ∃ y, activeB2 h x y) (k : ℕ) (hk : k < 2 * h - 1) :
  (row_map h hh x)^[k] (H_val h hh x) ≠ jump_y h hh x :=
by
  intro h_eq
  have ⟨k_min, hk_min_le, hk_min_eq, hk_min_prop⟩ := exists_minimal_k h hh x k h_eq
  have ⟨c, hc_ge, hc_eq⟩ := total_desc_eq_c h hh x h_act k_min hk_min_eq hk_min_prop
  have h_bound := total_desc_bound_min h hh x h_act k_min hk_min_eq hk_min_prop
  have hc_cases : c = 0 ∨ 1 ≤ c := by omega
  rcases hc_cases with rfl | hc_pos
  · have hc_zero : (total_desc h hh x k_min : ℤ) = H_sub_J h hh x := by omega
    exact c_eq_zero_impossible h hh x h_act k_min hk_min_eq hk_min_prop hc_zero
  · have hh_ge : 5 ≤ (h : ℤ) := by omega
    have h_c_mul : 2 * (h : ℤ) ≤ c * (2 * (h : ℤ)) := by nlinarith
    omega

theorem row_map_iter_not_jump (x : Fin (2 * h)) (k : ℕ) (hk : k < 2 * h - 1) :
  (row_map h hh x)^[k] (H_val h hh x) ≠ jump_y h hh x :=
by
  have h_cases := Classical.em (∃ y, activeB2 h x y)
  cases h_cases with
  | inl h_act =>
    exact row_map_active_not_jump h hh x h_act k hk
  | inr h_not =>
    have h_gen : ∀ y, ¬ activeB2 h x y := by
      intro y hy
      exact h_not ⟨y, hy⟩
    exact row_map_generic_not_jump h hh x h_gen k hk

theorem r2Map_iter_row (x : Fin (2 * h)) (k : ℕ) (hk : k < 2 * h) :
  (r2Map h hh)^[k] (x, H_val h hh x) = (x, (row_map h hh x)^[k] (H_val h hh x)) :=
by
  revert hk
  induction k with
  | zero =>
    intro _
    rfl
  | succ k ih =>
    intro hk
    have hk' : k < 2 * h := by omega
    have ih' := ih hk'
    have h1 : (r2Map h hh)^[k + 1] (x, H_val h hh x) = r2Map h hh ((r2Map h hh)^[k] (x, H_val h hh x)) :=
      Function.iterate_succ_apply' (r2Map h hh) k (x, H_val h hh x)
    have h2 : (row_map h hh x)^[k + 1] (H_val h hh x) = row_map h hh x ((row_map h hh x)^[k] (H_val h hh x)) :=
      Function.iterate_succ_apply' (row_map h hh x) k (H_val h hh x)
    rw [h1, h2, ih']
    have h_r2 : r2Map h hh (x, (row_map h hh x)^[k] (H_val h hh x)) =
      if (row_map h hh x)^[k] (H_val h hh x) = jump_y h hh x then
        (succ2c h hh x, H_val h hh (succ2c h hh x))
      else
        (x, row_map h hh x ((row_map h hh x)^[k] (H_val h hh x))) :=
      r2Map_eq h hh (x, (row_map h hh x)^[k] (H_val h hh x))
    rw [h_r2]
    have hk'' : k < 2 * h - 1 := by omega
    have not_jump := row_map_iter_not_jump h hh x k hk''
    rw [if_neg not_jump]

theorem row_map_generic_jump (x : Fin (2 * h)) (h_gen : ∀ y, ¬ activeB2 h x y) :
  (row_map h hh x)^[2 * h - 1] (H_val h hh x) = jump_y h hh x :=
by
  have h_2h_gt_1 : 1 < 2 * h := by omega
  letI : NeZero (2 * h) := ⟨by omega⟩

  have hx1 : x.val ≠ h + 1 := by
    intro h_eq
    let y : Fin (2 * h) := ⟨h - 1, by omega⟩
    have hy : y.val = h - 1 := rfl
    have h_act := h_gen y
    revert h_act
    unfold activeB2
    by_cases h_even : h % 2 = 0
    · rw [if_pos h_even]
      intro h_act
      apply h_act
      left
      exact ⟨h_eq, by omega⟩
    · rw [if_neg h_even]
      intro h_act
      apply h_act
      left
      exact ⟨h_eq, by omega⟩

  have hx4 : x.val ≠ h + 4 := by
    intro h_eq
    let y : Fin (2 * h) := ⟨h - 3, by omega⟩
    have hy : y.val = h - 3 := rfl
    have h_act := h_gen y
    revert h_act
    unfold activeB2
    by_cases h_even : h % 2 = 0
    · rw [if_pos h_even]
      intro h_act
      apply h_act
      right
      exact ⟨h_eq, by omega⟩
    · rw [if_neg h_even]
      intro h_act
      apply h_act
      right
      exact ⟨h_eq, by omega⟩

  have one2_eq : one2 h hh = 1 := by
    apply Fin.ext
    change 1 = 1 % (2 * h)
    symm
    apply Nat.mod_eq_of_lt
    omega

  have pred2c_eq_sub_one : ∀ v : Fin (2 * h), pred2c h hh v = v - 1 := by
    intro v
    unfold pred2c
    rw [one2_eq]

  have succ2c_eq_add_one : ∀ v : Fin (2 * h), succ2c h hh v = v + 1 := by
    intro v
    unfold succ2c
    rw [one2_eq]

  have val_pred2c : ∀ (v : Fin (2 * h)), v.val > 0 → (pred2c h hh v).val = v.val - 1 := by
    intro v hv
    rw [pred2c_eq_sub_one]
    apply Fin.val_sub_one_of_ne_zero
    intro h_eq
    have h_v_val : v.val = 0 := by
      rw [h_eq]
      rfl
    omega

  have pred2c_succ2c : ∀ v : Fin (2 * h), pred2c h hh (succ2c h hh v) = v := by
    intro v
    rw [succ2c_eq_add_one, pred2c_eq_sub_one]
    exact add_sub_cancel_right v 1

  have A2_generic : ∀ z : Fin (2 * h), ¬ y2SwitchRow h z → A2 h hh z = -z := by
    intro z hz
    have h_add : A2 h hh z + z = 0 := by
      apply Fin.ext
      unfold A2 y2star succ2c one2
      rw [if_neg hz]
      change (((2 * h - 1 - z.val) + 1) % (2 * h) + z.val) % (2 * h) = 0
      by_cases hz0 : z.val = 0
      · rw [hz0]
        have H2 : 2 * h - 1 - 0 + 1 = 2 * h := by omega
        rw [H2]
        have H3 : 2 * h % (2 * h) = 0 := Nat.mod_self (2 * h)
        rw [H3]
        have H4 : (0 + 0) % (2 * h) = 0 := rfl
        exact H4
      · have H2 : 2 * h - 1 - z.val + 1 = 2 * h - z.val := by omega
        rw [H2]
        have H3 : (2 * h - z.val) % (2 * h) = 2 * h - z.val := by apply Nat.mod_eq_of_lt; omega
        rw [H3]
        have H4 : 2 * h - z.val + z.val = 2 * h := by omega
        rw [H4]
        exact Nat.mod_self (2 * h)
    exact calc A2 h hh z = A2 h hh z + z - z := by rw [add_sub_cancel_right]
      _ = 0 - z := by rw [h_add]
      _ = -z := by rw [zero_sub]

  have A2_switch : ∀ z1 z2 : Fin (2 * h), y2SwitchRow h z1 → y2SwitchRow h z2 → A2 h hh z1 = A2 h hh z2 := by
    intro z1 z2 hz1 hz2
    unfold A2 y2star
    rw [if_pos hz1, if_pos hz2]

  have h_H_A2 : H_val h hh x = A2 h hh x := by
    by_cases hx2 : x.val = h + 2
    · have h_sw_x : y2SwitchRow h x := by unfold y2SwitchRow; right; left; exact hx2
      have px_eq : pred2c h hh x = ⟨h + 1, by omega⟩ := by
        apply Fin.ext
        have h_sub : (pred2c h hh x).val = x.val - 1 := val_pred2c x (by omega)
        have h_rhs : (⟨h + 1, by omega⟩ : Fin (2 * h)).val = h + 1 := rfl
        rw [h_sub, hx2, h_rhs]
        omega
      have h_sw_px : y2SwitchRow h (pred2c h hh x) := by
        unfold y2SwitchRow
        have h_sub : (pred2c h hh x).val = x.val - 1 := val_pred2c x (by omega)
        rw [h_sub, hx2]
        left
        omega
      have h_T_cond : (pred2c h hh x).val = h + 1 ∨ (pred2c h hh x).val = h + 2 := by
        left
        have h_sub : (pred2c h hh x).val = x.val - 1 := val_pred2c x (by omega)
        rw [h_sub, hx2]
        omega
      unfold H_val T_val
      rw [if_pos h_T_cond]
      apply A2_switch _ _ h_sw_px h_sw_x

    by_cases hx3 : x.val = h + 3
    · have h_sw_x : y2SwitchRow h x := by unfold y2SwitchRow; right; right; exact hx3
      have px_eq : pred2c h hh x = ⟨h + 2, by omega⟩ := by
        apply Fin.ext
        have h_sub : (pred2c h hh x).val = x.val - 1 := val_pred2c x (by omega)
        have h_rhs : (⟨h + 2, by omega⟩ : Fin (2 * h)).val = h + 2 := rfl
        rw [h_sub, hx3, h_rhs]
        omega
      have h_sw_px : y2SwitchRow h (pred2c h hh x) := by
        unfold y2SwitchRow
        have h_sub : (pred2c h hh x).val = x.val - 1 := val_pred2c x (by omega)
        rw [h_sub, hx3]
        right; left
        omega
      have h_T_cond : (pred2c h hh x).val = h + 1 ∨ (pred2c h hh x).val = h + 2 := by
        right
        have h_sub : (pred2c h hh x).val = x.val - 1 := val_pred2c x (by omega)
        rw [h_sub, hx3]
        omega
      unfold H_val T_val
      rw [if_pos h_T_cond]
      apply A2_switch _ _ h_sw_px h_sw_x

    have hx2_not : x.val ≠ h + 2 := hx2
    have hx3_not : x.val ≠ h + 3 := hx3
    have h_sw_x : ¬ y2SwitchRow h x := by
      unfold y2SwitchRow
      push_neg
      exact ⟨hx1, hx2_not, hx3_not⟩

    have h_px_val : (pred2c h hh x).val = x.val - 1 ∨ (pred2c h hh x).val = 2 * h - 1 := by
      by_cases hx0 : x.val = 0
      · right
        have h_eq : pred2c h hh x = mMinusOne2 h hh := by
          rw [pred2c_eq_sub_one]
          have h1 : x = 0 := by ext; exact hx0
          rw [h1, zero_sub]
          symm
          apply eq_neg_of_add_eq_zero_left
          apply Fin.ext
          have hv1 : (mMinusOne2 h hh).val = 2 * h - 1 := rfl
          have hv2 : (1 : Fin (2 * h)).val = 1 := by
            change 1 % (2 * h) = 1
            apply Nat.mod_eq_of_lt
            omega
          change ((mMinusOne2 h hh).val + (1 : Fin (2 * h)).val) % (2 * h) = 0
          rw [hv1, hv2]
          have H : 2 * h - 1 + 1 = 2 * h := by omega
          rw [H]
          exact Nat.mod_self (2 * h)
        rw [h_eq]
        rfl
      · left
        apply val_pred2c
        omega

    have h_sw_px : ¬ y2SwitchRow h (pred2c h hh x) := by
      unfold y2SwitchRow
      push_neg
      rcases h_px_val with hval | hval
      · refine ⟨by omega, by omega, by omega⟩
      · refine ⟨by omega, by omega, by omega⟩

    have h_T_cond : ¬ ((pred2c h hh x).val = h + 1 ∨ (pred2c h hh x).val = h + 2) := by
      rcases h_px_val with hval | hval
      · intro h_or; rcases h_or with heq | heq <;> omega
      · intro h_or; rcases h_or with heq | heq <;> omega

    unfold H_val T_val
    rw [if_neg h_T_cond]
    rw [A2_generic (pred2c h hh x) h_sw_px]
    rw [A2_generic x h_sw_x]
    rw [pred2c_eq_sub_one, pred2c_eq_sub_one]
    have neg_sub_eq : -(x - 1) = -x + 1 := by
      exact calc -(x - 1) = 1 - x := by rw [neg_sub]
        _ = 1 + -x := by rw [sub_eq_add_neg]
        _ = -x + 1 := by rw [add_comm]
    rw [neg_sub_eq]
    exact add_sub_cancel_right (-x) 1

  have row_map_eq : ∀ y, row_map h hh x y = pred2c h hh y := by
    intro y
    unfold row_map
    by_cases hy : y = jump_y h hh x
    · rw [if_pos hy]
      unfold jump_y at hy
      rw [hy, pred2c_succ2c]
      exact h_H_A2
    · rw [if_neg hy]
      have h_not_act := h_gen (pred2c h hh y)
      rw [if_neg h_not_act]

  have h_iter_row_map : ∀ (k : ℕ) (v : Fin (2 * h)), (row_map h hh x)^[k] v = (pred2c h hh)^[k] v := by
    intro k
    induction k with
    | zero =>
      intro v; rfl
    | succ k ih =>
      intro v
      change (row_map h hh x)^[k] (row_map h hh x v) = (pred2c h hh)^[k] (pred2c h hh v)
      rw [row_map_eq]
      rw [ih (pred2c h hh v)]

  have iter_pred2c_eq : ∀ (k : ℕ) (v : Fin (2 * h)), (pred2c h hh)^[k] v = v - natToFin h hh k := by
    intro k
    induction k with
    | zero =>
      intro v
      change v = v - natToFin h hh 0
      have H0 : natToFin h hh 0 = 0 := rfl
      rw [H0, sub_zero]
    | succ k ih =>
      intro v
      change (pred2c h hh)^[k] (pred2c h hh v) = v - natToFin h hh (k + 1)
      rw [ih (pred2c h hh v)]
      rw [pred2c_eq_sub_one]
      have h_add : natToFin h hh (k + 1) = natToFin h hh k + 1 := by
        apply Fin.ext
        have hL : (natToFin h hh (k + 1)).val = (k + 1) % (2 * h) := rfl
        have hR : (natToFin h hh k + 1).val = ((k % (2 * h)) + 1) % (2 * h) := by
          change ((k % (2 * h)) + (1 : Fin (2 * h)).val) % (2 * h) = _
          have h1 : (1 : Fin (2 * h)).val = 1 := by
            change 1 % (2 * h) = 1
            apply Nat.mod_eq_of_lt
            omega
          rw [h1]
        rw [hL, hR]
        have H_add := Nat.add_mod k 1 (2 * h)
        have H_one : 1 % (2 * h) = 1 := by apply Nat.mod_eq_of_lt; omega
        rw [H_one] at H_add
        exact H_add
      rw [h_add]
      exact calc v - 1 - natToFin h hh k = v - (1 + natToFin h hh k) := by rw [sub_sub]
        _ = v - (natToFin h hh k + 1) := by rw [add_comm 1 (natToFin h hh k)]

  have h_pred2c_2h_minus_1 : ∀ v : Fin (2 * h), (pred2c h hh)^[2 * h - 1] v = succ2c h hh v := by
    intro v
    rw [iter_pred2c_eq]
    rw [succ2c_eq_add_one]
    have h_natToFin : natToFin h hh (2 * h - 1) = -1 := by
      apply eq_neg_of_add_eq_zero_left
      apply Fin.ext
      have hv1 : (natToFin h hh (2 * h - 1)).val = 2 * h - 1 := by
        unfold natToFin
        apply Nat.mod_eq_of_lt
        omega
      have hv2 : (1 : Fin (2 * h)).val = 1 := by
        change 1 % (2 * h) = 1
        apply Nat.mod_eq_of_lt
        omega
      change ((natToFin h hh (2 * h - 1)).val + (1 : Fin (2 * h)).val) % (2 * h) = 0
      rw [hv1, hv2]
      have H3 : 2 * h - 1 + 1 = 2 * h := by omega
      rw [H3]
      exact Nat.mod_self (2 * h)
    rw [h_natToFin]
    exact calc v - -1 = v + -(-1) := by rw [sub_eq_add_neg]
      _ = v + 1 := by rw [neg_neg]

  rw [h_iter_row_map]
  rw [h_pred2c_2h_minus_1]
  rw [h_H_A2]
  rfl

theorem activeB2_x_val (h : ℕ) (x y : Fin (2 * h)) (h_act : activeB2 h x y) :
  x.val = h + 1 ∨ x.val = h + 4 :=
by
  unfold activeB2 at h_act
  split at h_act
  · rcases h_act with ⟨h1, _⟩ | ⟨h4, _⟩
    · left
      exact h1
    · right
      exact h4
  · rcases h_act with ⟨h1, _⟩ | ⟨h4, _⟩
    · left
      exact h1
    · right
      exact h4

theorem jump_y_h_plus_1_even_val (h : ℕ) (hh : 5 ≤ h) (x : Fin (2 * h)) (hx : x.val = h + 1) (heven : h % 2 = 0) :
  (jump_y h hh x).val = 0 :=
by
  unfold jump_y A2 succ2c y2star
  have h_switch : y2SwitchRow h x := by
    unfold y2SwitchRow
    exact Or.inl hx
  rw [if_pos h_switch, if_pos heven]
  unfold mMinusTwo2 one2
  change (((2 * h - 2 + 1) % (2 * h)) + 1) % (2 * h) = 0
  have h_lt : (2 * h - 2 + 1) < 2 * h := by omega
  rw [Nat.mod_eq_of_lt h_lt]
  have h_eq : (2 * h - 2 + 1) + 1 = 2 * h := by omega
  rw [h_eq]
  exact Nat.mod_self (2 * h)

theorem jump_y_h_plus_1_odd_val (h : ℕ) (hh : 5 ≤ h) (x : Fin (2 * h)) (hx : x.val = h + 1) (hodd : ¬ (h % 2 = 0)) :
  (jump_y h hh x).val = 1 :=
by
  have h_switch : y2SwitchRow h x := by
    unfold y2SwitchRow
    omega
  unfold jump_y A2 succ2c y2star
  simp only [h_switch, hodd, if_true, if_false, ite_true, ite_false]
  unfold mMinusOne2 one2
  change (((2 * h - 1 + 1) % (2 * h) + 1) % (2 * h) = 1)
  have h1 : 2 * h - 1 + 1 = 2 * h := by omega
  rw [h1, Nat.mod_self]
  have h2 : 1 < 2 * h := by omega
  change 1 % (2 * h) = 1
  exact Nat.mod_eq_of_lt h2

theorem jump_y_h_plus_4_val (h : ℕ) (hh : 5 ≤ h) (x : Fin (2 * h)) (hx : x.val = h + 4) :
  ((jump_y h hh x).val : ℤ) = (h : ℤ) - 3 :=
by
  have h_y2star_val : (y2star h hh x).val = h - 5 := by
    unfold y2star
    have h_not : ¬ y2SwitchRow h x := by
      unfold y2SwitchRow
      omega
    simp [h_not]
    omega

  have h_A2_val : (A2 h hh x).val = h - 4 := by
    unfold A2 succ2c one2
    change ((y2star h hh x).val + 1) % (2 * h) = h - 4
    rw [h_y2star_val]
    have h_eq1 : h - 5 + 1 = h - 4 := by omega
    rw [h_eq1]
    apply Nat.mod_eq_of_lt
    omega

  have h_jump_val : (jump_y h hh x).val = h - 3 := by
    unfold jump_y succ2c one2
    change ((A2 h hh x).val + 1) % (2 * h) = h - 3
    rw [h_A2_val]
    have h_eq2 : h - 4 + 1 = h - 3 := by omega
    rw [h_eq2]
    apply Nat.mod_eq_of_lt
    omega

  rw [h_jump_val]
  omega

theorem jump_y_eq_a_act_lem (x : Fin (2 * h)) (h_act : ∃ y, activeB2 h x y) :
  jump_y h hh x = a_act h hh x :=
by
  obtain ⟨y, hy⟩ := h_act
  have h_val : x.val = h + 1 ∨ x.val = h + 4 := activeB2_x_val h x y hy
  apply Fin.ext
  rcases h_val with hx | hx
  · by_cases heven : h % 2 = 0
    · have h1 := jump_y_h_plus_1_even_val h hh x hx heven
      rw [h1]
      have h_a : (a_act h hh x).val = 0 := by
        unfold a_act
        simp [hx, heven]
      exact h_a.symm
    · have h2 := jump_y_h_plus_1_odd_val h hh x hx heven
      rw [h2]
      have h_a : (a_act h hh x).val = 1 := by
        unfold a_act
        simp [hx, heven]
      exact h_a.symm
  · have h3 := jump_y_h_plus_4_val h hh x hx
    have h_not : x.val ≠ h + 1 := by omega
    have h_a : (a_act h hh x).val = h - 3 := by
      unfold a_act
      simp [h_not]
    omega

theorem track1_mod_helper (B H K : ℕ) (h1 : 2 * K ≤ B) (h2 : B < 2 * H) :
  (B + 2 * H - (2 * K) % (2 * H)) % (2 * H) = B - 2 * K :=
by
  have hk : 2 * K < 2 * H := by omega
  have eq1 : (2 * K) % (2 * H) = 2 * K := Nat.mod_eq_of_lt hk
  rw [eq1]
  have eq2 : B + 2 * H - 2 * K = B - 2 * K + 2 * H := by omega
  rw [eq2, Nat.add_mod_right]
  have hk2 : B - 2 * K < 2 * H := by omega
  exact Nat.mod_eq_of_lt hk2

theorem track1_b_act_bound (x : Fin (2 * h)) (k : ℕ) (hk : k ≤ k_track1 h hh x) :
  2 * k ≤ (b_act h hh x).val ∧ (b_act h hh x).val < 2 * h :=
by
  unfold k_track1 L_act at hk
  unfold b_act
  split_ifs at hk ⊢ <;> dsimp at hk ⊢ <;> omega

theorem track1_state_val_lem (x : Fin (2 * h)) (h_act : ∃ y, activeB2 h x y) (k : ℕ) (hk : k ≤ k_track1 h hh x) :
  (track1_state h hh x k).val + 2 * k = (b_act h hh x).val :=
by
  have ⟨hb1, hb2⟩ := track1_b_act_bound h hh x k hk
  have h_mod := track1_mod_helper ((b_act h hh x).val) h k hb1 hb2
  dsimp [track1_state]
  rw [h_mod]
  omega

theorem track1_k_strict_bounds_lem (x : Fin (2 * h)) (h_act : ∃ y, activeB2 h x y) (k : ℕ) (hk : k < k_track1 h hh x) :
  (a_act h hh x).val + 3 + 2 * k ≤ (b_act h hh x).val :=
by
  rcases h_act with ⟨y, hy⟩
  unfold activeB2 at hy
  unfold k_track1 at hk
  unfold L_act at hk
  unfold a_act b_act
  dsimp at *
  split_ifs at hy hk ⊢ <;> dsimp at * <;> omega

theorem track1_state_not_jump (x : Fin (2 * h)) (h_act : ∃ y, activeB2 h x y) (k : ℕ) (hk : k < k_track1 h hh x) :
  track1_state h hh x k ≠ jump_y h hh x :=
by
  intro heq
  have heq_val : (track1_state h hh x k).val = (jump_y h hh x).val := by rw [heq]
  have h1 := jump_y_eq_a_act_lem h hh x h_act
  have h1_val : (jump_y h hh x).val = (a_act h hh x).val := by rw [h1]
  have hk_le : k ≤ k_track1 h hh x := Nat.le_of_lt hk
  have h2 := track1_state_val_lem h hh x h_act k hk_le
  have h3 := track1_k_strict_bounds_lem h hh x h_act k hk
  rw [heq_val, h1_val] at h2
  omega

theorem pred2c_val_of_ge_one (y : Fin (2 * h)) (hy : 1 ≤ y.val) :
  (pred2c h hh y).val + 1 = y.val :=
by
  have h_lt : y.val < 2 * h := y.isLt
  have h_pos : 0 < 2 * h := by omega
  have H : (pred2c h hh y).val = y.val - 1 := by
    unfold pred2c
    have eq1 : (y - one2 h hh).val = (2 * h + (y.val - 1)) % (2 * h) := by
      rw [Fin.sub_def]
      have h_one : (one2 h hh).val = 1 := rfl
      rw [h_one]
      apply congrArg (fun x => x % (2 * h))
      omega
    rw [eq1]
    rw [Nat.add_mod, Nat.mod_self, Nat.zero_add, Nat.mod_mod]
    exact Nat.mod_eq_of_lt (by omega)
  omega

theorem track1_state_val_ge_one (x : Fin (2 * h)) (h_act : ∃ y, activeB2 h x y) (k : ℕ) (hk : k < k_track1 h hh x) :
  1 ≤ (track1_state h hh x k).val :=
by
  have hk_le : k ≤ k_track1 h hh x := by omega
  have h1 := track1_state_val_lem h hh x h_act k hk_le
  have h2 := track1_k_strict_bounds_lem h hh x h_act k hk
  omega

theorem track1_state_pred_val_helper (x : Fin (2 * h)) (h_act : ∃ y, activeB2 h x y) (k : ℕ) (hk : k < k_track1 h hh x) :
  (pred2c h hh (track1_state h hh x k)).val + 2 * k + 1 = (b_act h hh x).val :=
by
  have h1 := track1_state_val_ge_one h hh x h_act k hk
  have h2 := pred2c_val_of_ge_one h hh (track1_state h hh x k) h1
  have hk_le : k ≤ k_track1 h hh x := by omega
  have h3 := track1_state_val_lem h hh x h_act k hk_le
  omega

theorem track1_k_strict_bounds_helper (x : Fin (2 * h)) (h_act : ∃ y, activeB2 h x y) (k : ℕ) (hk : k < k_track1 h hh x) :
  (a_act h hh x).val + 3 + 2 * k ≤ (b_act h hh x).val :=
by
  obtain ⟨y, hy⟩ := h_act
  dsimp [activeB2] at hy
  dsimp [k_track1, L_act] at hk
  dsimp [a_act, b_act]
  split_ifs at hy with hp
  · rcases hy with ⟨hx, _⟩ | ⟨hx, _⟩
    · split_ifs at hk ⊢ <;> dsimp only at hk ⊢ <;> omega
    · split_ifs at hk ⊢ <;> dsimp only at hk ⊢ <;> omega
  · rcases hy with ⟨hx, _⟩ | ⟨hx, _⟩
    · split_ifs at hk ⊢ <;> dsimp only at hk ⊢ <;> omega
    · split_ifs at hk ⊢ <;> dsimp only at hk ⊢ <;> omega

theorem activeB2_iff_in_interval_helper (x y : Fin (2 * h)) (h_act : ∃ u, activeB2 h x u) :
  activeB2 h x y ↔ (a_act h hh x).val ≤ y.val ∧ y.val ≤ (b_act h hh x).val :=
by
  have h_five : 5 ≤ h := hh
  rcases h_act with ⟨u, hu⟩
  have hy : y.val < 2 * h := y.isLt
  have hx : x.val < 2 * h := x.isLt
  have hu_lt : u.val < 2 * h := u.isLt
  unfold activeB2 at hu ⊢
  unfold a_act b_act
  by_cases h_mod : h % 2 = 0 <;> by_cases h_x : x.val = h + 1 <;>
    simp [h_mod, h_x] at hu ⊢ <;> omega

theorem track1_state_active (x : Fin (2 * h)) (h_act : ∃ y, activeB2 h x y) (k : ℕ) (hk : k < k_track1 h hh x) :
  activeB2 h x (pred2c h hh (track1_state h hh x k)) :=
by
  rw [activeB2_iff_in_interval_helper h hh x (pred2c h hh (track1_state h hh x k)) h_act]
  have h1 := track1_state_pred_val_helper h hh x h_act k hk
  have h2 := track1_k_strict_bounds_helper h hh x h_act k hk
  omega

theorem track1_step_eq_pred2c_pred2c (x : Fin (2 * h)) (h_act : ∃ y, activeB2 h x y) (k : ℕ) (hk : k < k_track1 h hh x) :
  row_map h hh x (track1_state h hh x k) = pred2c h hh (pred2c h hh (track1_state h hh x k)) :=
by
  unfold row_map
  have h1 := track1_state_not_jump h hh x h_act k hk
  have h2 := track1_state_active h hh x h_act k hk
  rw [if_neg h1, if_pos h2]

theorem pred2c_pred2c_track1_state (x : Fin (2 * h)) (h_act : ∃ y, activeB2 h x y) (k : ℕ) (hk : k < k_track1 h hh x) :
  pred2c h hh (pred2c h hh (track1_state h hh x k)) = track1_state h hh x (k + 1) :=
by
  have hk_bound : 2 * k + 2 < 2 * h := by
    have h_L_act : L_act h hh x = if x.val = h + 1 then (if h % 2 = 0 then h - 1 else h - 2) else (if h % 2 = 0 then h + 1 else h + 2) := rfl
    have hL : L_act h hh x ≤ h + 2 := by
      rw [h_L_act]
      split <;> split <;> omega
    have h_k_track1 : k_track1 h hh x = (L_act h hh x - 1) / 2 := rfl
    have hk_ineq : k < (L_act h hh x - 1) / 2 := by
      rw [h_k_track1] at hk
      exact hk
    omega

  have h2k : (2 * k) % (2 * h) = 2 * k := Nat.mod_eq_of_lt (by omega)

  have h2k2 : (2 * (k + 1)) % (2 * h) = 2 * k + 2 := by
    have h_eq : 2 * (k + 1) = 2 * k + 2 := by omega
    rw [h_eq]
    exact Nat.mod_eq_of_lt hk_bound

  have h_val_k : (track1_state h hh x k).val = ((b_act h hh x).val + 2 * h - 2 * k) % (2 * h) := by
    change ((b_act h hh x).val + 2 * h - (2 * k) % (2 * h)) % (2 * h) = _
    rw [h2k]

  have h_val_k1 : (track1_state h hh x (k + 1)).val = ((b_act h hh x).val + 2 * h - (2 * k + 2)) % (2 * h) := by
    change ((b_act h hh x).val + 2 * h - (2 * (k + 1)) % (2 * h)) % (2 * h) = _
    rw [h2k2]

  have H_val : (track1_state h hh x k).val = ((track1_state h hh x (k + 1)).val + 2) % (2 * h) := by
    rw [h_val_k, h_val_k1]
    have h_add : (b_act h hh x).val + 2 * h - 2 * k = (b_act h hh x).val + 2 * h - (2 * k + 2) + 2 := by omega
    rw [h_add]
    have h_mod := Nat.add_mod ((b_act h hh x).val + 2 * h - (2 * k + 2)) 2 (2 * h)
    have h2 : 2 % (2 * h) = 2 := Nat.mod_eq_of_lt (by omega)
    rw [h2] at h_mod
    exact h_mod

  have h_mod_1 (v : ℕ) : (((v + 1) % (2 * h)) + 1) % (2 * h) = (v + 2) % (2 * h) := by
    have h_add_mod := Nat.add_mod (v + 1) 1 (2 * h)
    have h1 : 1 % (2 * h) = 1 := Nat.mod_eq_of_lt (by omega)
    rw [h1] at h_add_mod
    have h_eq : v + 1 + 1 = v + 2 := by omega
    rw [h_eq] at h_add_mod
    exact h_add_mod.symm

  have H_fin : track1_state h hh x (k + 1) + one2 h hh + one2 h hh = track1_state h hh x k := by
    apply Fin.ext
    have h_one2 : (one2 h hh).val = 1 := rfl
    have val_add (A B : Fin (2 * h)) : (A + B).val = (A.val + B.val) % (2 * h) := rfl
    rw [val_add, val_add, h_one2]
    exact (h_mod_1 _).trans H_val.symm

  haveI : NeZero (2 * h) := ⟨by omega⟩
  unfold pred2c
  rw [← H_fin, add_sub_cancel_right, add_sub_cancel_right]

theorem track1_step_eq (x : Fin (2 * h)) (h_act : ∃ y, activeB2 h x y) (k : ℕ) (hk : k < k_track1 h hh x) :
  row_map h hh x (track1_state h hh x k) = track1_state h hh x (k + 1) :=
Eq.trans (track1_step_eq_pred2c_pred2c h hh x h_act k hk) (pred2c_pred2c_track1_state h hh x h_act k hk)

theorem track1_state_zero (h : ℕ) (hh : 5 ≤ h) (x : Fin (2 * h)) : track1_state h hh x 0 = b_act h hh x :=
by
  ext
  change (((b_act h hh x).val + 2 * h - (2 * 0) % (2 * h)) % (2 * h)) = (b_act h hh x).val
  have h0 : (2 * 0) % (2 * h) = 0 := by simp
  rw [h0]
  have h1 : (b_act h hh x).val + 2 * h - 0 = (b_act h hh x).val + 2 * h := by omega
  rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (b_act h hh x).isLt]

theorem track1_iter_eq (x : Fin (2 * h)) (h_act : ∃ y, activeB2 h x y) (k : ℕ) (hk : k ≤ k_track1 h hh x) :
  (row_map h hh x)^[k] (b_act h hh x) = track1_state h hh x k :=
by
  revert hk
  induction k with
  | zero =>
    intro _
    rw [track1_state_zero h hh x]
    rw [Function.iterate_zero_apply]
  | succ n ih =>
    intro hk
    have hn1 : n ≤ k_track1 h hh x := by omega
    have hn2 : n < k_track1 h hh x := by omega
    rw [iterate_succ_out]
    rw [ih hn1]
    exact track1_step_eq h hh x h_act n hn2

theorem track1_end_eq (x : Fin (2 * h)) (h_act : ∃ y, activeB2 h x y) :
  track1_state h hh x (k_track1 h hh x) = state_y1 h hh x :=
by
  obtain ⟨y, hy⟩ := h_act
  have hx : x.val = h + 1 ∨ x.val = h + 4 := by
    unfold activeB2 at hy
    split_ifs at hy with h_even
    · rcases hy with ⟨h1, _⟩ | ⟨h4, _⟩
      · left; exact h1
      · right; exact h4
    · rcases hy with ⟨h1, _⟩ | ⟨h4, _⟩
      · left; exact h1
      · right; exact h4

  have h_mod2 : h % 2 = 0 ∨ h % 2 = 1 := by omega

  ext
  change (((b_act h hh x).val + 2 * h - (2 * (k_track1 h hh x)) % (2 * h)) % (2 * h)) =
         (((a_act h hh x).val + 1) % (2 * h))
  unfold a_act b_act k_track1 L_act

  rcases h_mod2 with hm0 | hm1
  · rcases hx with hx1 | hx4
    · have hx_eq : (x.val = h + 1) = True := eq_true hx1
      have hm0_eq : (h % 2 = 0) = True := eq_true hm0
      simp only [hx_eq, hm0_eq, if_true, if_false]
      change (h - 1 + 2 * h - 2 * ((h - 1 - 1) / 2) % (2 * h)) % (2 * h) = (0 + 1) % (2 * h)
      have h_div : 2 * ((h - 1 - 1) / 2) = h - 2 := by omega
      have mod1 : (h - 2) % (2 * h) = h - 2 := by
        apply Nat.mod_eq_of_lt; omega
      have eq1 : h - 1 + 2 * h - (h - 2) = 2 * h + 1 := by omega
      rw [h_div, mod1, eq1]
      have eq2 : (2 * h + 1) % (2 * h) = 1 % (2 * h) := by
        rw [Nat.add_mod, Nat.mod_self, Nat.zero_add, Nat.mod_mod]
      have eq3 : (0 + 1) % (2 * h) = 1 % (2 * h) := rfl
      rw [eq2, eq3]
    · have hx_neg : ¬(x.val = h + 1) := by omega
      have hx_eq : (x.val = h + 1) = False := eq_false hx_neg
      have hm0_eq : (h % 2 = 0) = True := eq_true hm0
      simp only [hx_eq, hm0_eq, if_true, if_false]
      change (2 * h - 2 + 2 * h - 2 * ((h + 1 - 1) / 2) % (2 * h)) % (2 * h) = (h - 3 + 1) % (2 * h)
      have h_div : 2 * ((h + 1 - 1) / 2) = h := by omega
      have mod1 : h % (2 * h) = h := by
        apply Nat.mod_eq_of_lt; omega
      have eq1 : 2 * h - 2 + 2 * h - h = 2 * h + (h - 2) := by omega
      rw [h_div, mod1, eq1]
      have eq2 : (2 * h + (h - 2)) % (2 * h) = (h - 2) % (2 * h) := by
        rw [Nat.add_mod, Nat.mod_self, Nat.zero_add, Nat.mod_mod]
      have eq3 : (h - 3 + 1) % (2 * h) = (h - 2) % (2 * h) := by
        have : h - 3 + 1 = h - 2 := by omega
        rw [this]
      rw [eq2, eq3]
  · rcases hx with hx1 | hx4
    · have hx_eq : (x.val = h + 1) = True := eq_true hx1
      have hm0_neg : ¬(h % 2 = 0) := by omega
      have hm0_eq : (h % 2 = 0) = False := eq_false hm0_neg
      simp only [hx_eq, hm0_eq, if_true, if_false]
      change (h - 1 + 2 * h - 2 * ((h - 2 - 1) / 2) % (2 * h)) % (2 * h) = (1 + 1) % (2 * h)
      have h_div : 2 * ((h - 2 - 1) / 2) = h - 3 := by omega
      have mod1 : (h - 3) % (2 * h) = h - 3 := by
        apply Nat.mod_eq_of_lt; omega
      have eq1 : h - 1 + 2 * h - (h - 3) = 2 * h + 2 := by omega
      rw [h_div, mod1, eq1]
      have eq2 : (2 * h + 2) % (2 * h) = 2 % (2 * h) := by
        rw [Nat.add_mod, Nat.mod_self, Nat.zero_add, Nat.mod_mod]
      have eq3 : (1 + 1) % (2 * h) = 2 % (2 * h) := rfl
      rw [eq2, eq3]
    · have hx_neg : ¬(x.val = h + 1) := by omega
      have hx_eq : (x.val = h + 1) = False := eq_false hx_neg
      have hm0_neg : ¬(h % 2 = 0) := by omega
      have hm0_eq : (h % 2 = 0) = False := eq_false hm0_neg
      simp only [hx_eq, hm0_eq, if_true, if_false]
      change (2 * h - 1 + 2 * h - 2 * ((h + 2 - 1) / 2) % (2 * h)) % (2 * h) = (h - 3 + 1) % (2 * h)
      have h_div : 2 * ((h + 2 - 1) / 2) = h + 1 := by omega
      have mod1 : (h + 1) % (2 * h) = h + 1 := by
        apply Nat.mod_eq_of_lt; omega
      have eq1 : 2 * h - 1 + 2 * h - (h + 1) = 2 * h + (h - 2) := by omega
      rw [h_div, mod1, eq1]
      have eq2 : (2 * h + (h - 2)) % (2 * h) = (h - 2) % (2 * h) := by
        rw [Nat.add_mod, Nat.mod_self, Nat.zero_add, Nat.mod_mod]
      have eq3 : (h - 3 + 1) % (2 * h) = (h - 2) % (2 * h) := by
        have : h - 3 + 1 = h - 2 := by omega
        rw [this]
      rw [eq2, eq3]

theorem phase1_track1 (x : Fin (2 * h)) (h_act : ∃ y, activeB2 h x y) :
  (row_map h hh x)^[k_track1 h hh x] (H_val h hh x) = state_y1 h hh x :=
by
  rw [H_val_eq_b_act h hh x h_act]
  rw [track1_iter_eq h hh x h_act (k_track1 h hh x) (Nat.le_refl _)]
  exact track1_end_eq h hh x h_act

theorem phase2_trans_out (x : Fin (2 * h)) (h_act : ∃ y, activeB2 h x y) :
  (row_map h hh x)^[k_trans_out h hh x] (state_y1 h hh x) = state_y2 h hh x :=
by
  change row_map h hh x (state_y1 h hh x) = state_y2 h hh x
  have hx_cases : (x.val = h + 1 ∧ h % 2 = 0) ∨ (x.val = h + 1 ∧ h % 2 = 1) ∨ (x.val = h + 4 ∧ h % 2 = 0) ∨ (x.val = h + 4 ∧ h % 2 = 1) := by
    rcases h_act with ⟨y, hy⟩
    unfold activeB2 at hy
    by_cases h_mod : h % 2 = 0
    · rw [if_pos h_mod] at hy
      rcases hy with ⟨hx, _⟩ | ⟨hx, _⟩
      · left; exact ⟨hx, h_mod⟩
      · right; right; left; exact ⟨hx, h_mod⟩
    · rw [if_neg h_mod] at hy
      have h_mod1 : h % 2 = 1 := by omega
      rcases hy with ⟨hx, _⟩ | ⟨hx, _⟩
      · right; left; exact ⟨hx, h_mod1⟩
      · right; right; right; exact ⟨hx, h_mod1⟩

  rcases hx_cases with ⟨hx1, hm0⟩ | ⟨hx1, hm1⟩ | ⟨hx4, hm0⟩ | ⟨hx4, hm1⟩
  · -- Case 1: x.val = h + 1, h % 2 = 0
    have ha : a_act h hh x = ⟨0, by omega⟩ := by
      unfold a_act
      rw [if_pos hx1, if_pos hm0]
    have hs1 : state_y1 h hh x = ⟨1, by omega⟩ := by
      unfold state_y1 succ2c one2
      rw [ha]
      ext
      change (0 + 1) % (2 * h) = 1
      have h_lt : 0 + 1 < 2 * h := by omega
      exact Nat.mod_eq_of_lt h_lt
    have hy2 : y2SwitchRow h x := by unfold y2SwitchRow; left; exact hx1
    have hj : jump_y h hh x = ⟨0, by omega⟩ := by
      unfold jump_y A2 y2star mMinusTwo2 succ2c one2
      rw [if_pos hy2, if_pos hm0]
      ext
      change ((2 * h - 2 + 1) % (2 * h) + 1) % (2 * h) = 0
      have h1 : 2 * h - 2 + 1 = 2 * h - 1 := by omega
      rw [h1]
      have h2 : 2 * h - 1 < 2 * h := by omega
      rw [Nat.mod_eq_of_lt h2]
      have h3 : 2 * h - 1 + 1 = 2 * h := by omega
      rw [h3]
      exact Nat.mod_self (2 * h)
    have hy_neq : state_y1 h hh x ≠ jump_y h hh x := by
      rw [hs1, hj]
      intro h_eq
      have h_eq_val : 1 = 0 := congrArg Fin.val h_eq
      contradiction
    have h_pred : pred2c h hh (state_y1 h hh x) = a_act h hh x := by
      rw [hs1, ha]
      unfold pred2c one2
      ext
      have h1 : (2 * h - 1 + 1) % (2 * h) = 0 := by
        have heq : 2 * h - 1 + 1 = 2 * h := by omega
        rw [heq]
        exact Nat.mod_self (2 * h)
      have h2 : (1 + (2 * h - 1) % (2 * h)) % (2 * h) = 0 := by
        have h_mod : (2 * h - 1) % (2 * h) = 2 * h - 1 := by apply Nat.mod_eq_of_lt; omega
        rw [h_mod]
        have heq : 1 + (2 * h - 1) = 2 * h := by omega
        rw [heq]
        exact Nat.mod_self (2 * h)
      have h3 : (1 + (2 * h - 1)) % (2 * h) = 0 := by
        have heq : 1 + (2 * h - 1) = 2 * h := by omega
        rw [heq]
        exact Nat.mod_self (2 * h)
      first | rfl | exact h1 | exact h2 | exact h3
    have hact : activeB2 h x (pred2c h hh (state_y1 h hh x)) := by
      unfold activeB2
      rw [if_pos hm0]
      left
      constructor
      · exact hx1
      · rw [h_pred, ha]
        change 0 ≤ h - 1
        omega
    unfold row_map
    rw [if_neg hy_neq, if_pos hact]
    unfold state_y2
    rw [h_pred]

  · -- Case 2: x.val = h + 1, h % 2 = 1
    have hm0_neg : ¬ (h % 2 = 0) := by omega
    have ha : a_act h hh x = ⟨1, by omega⟩ := by
      unfold a_act
      rw [if_pos hx1, if_neg hm0_neg]
    have hs1 : state_y1 h hh x = ⟨2, by omega⟩ := by
      unfold state_y1 succ2c one2
      rw [ha]
      ext
      change (1 + 1) % (2 * h) = 2
      have h_lt : 2 < 2 * h := by omega
      exact Nat.mod_eq_of_lt h_lt
    have hy2 : y2SwitchRow h x := by unfold y2SwitchRow; left; exact hx1
    have hj : jump_y h hh x = ⟨1, by omega⟩ := by
      unfold jump_y A2 y2star mMinusOne2 succ2c one2
      rw [if_pos hy2, if_neg hm0_neg]
      ext
      change ((2 * h - 1 + 1) % (2 * h) + 1) % (2 * h) = 1
      have h1 : 2 * h - 1 + 1 = 2 * h := by omega
      rw [h1]
      rw [Nat.mod_self (2 * h)]
      have h2 : 0 + 1 = 1 := by omega
      rw [h2]
      have h_lt : 1 < 2 * h := by omega
      exact Nat.mod_eq_of_lt h_lt
    have hy_neq : state_y1 h hh x ≠ jump_y h hh x := by
      rw [hs1, hj]
      intro h_eq
      have h_eq_val : 2 = 1 := congrArg Fin.val h_eq
      contradiction
    have h_pred : pred2c h hh (state_y1 h hh x) = a_act h hh x := by
      rw [hs1, ha]
      unfold pred2c one2
      ext
      have h1 : (2 * h - 1 + 2) % (2 * h) = 1 := by
        have heq : 2 * h - 1 + 2 = 1 + 2 * h := by omega
        rw [heq, Nat.add_mod_right]
        apply Nat.mod_eq_of_lt
        omega
      have h2 : (2 + (2 * h - 1) % (2 * h)) % (2 * h) = 1 := by
        have h_mod : (2 * h - 1) % (2 * h) = 2 * h - 1 := by apply Nat.mod_eq_of_lt; omega
        rw [h_mod]
        have heq : 2 + (2 * h - 1) = 1 + 2 * h := by omega
        rw [heq, Nat.add_mod_right]
        apply Nat.mod_eq_of_lt
        omega
      have h3 : (2 + (2 * h - 1)) % (2 * h) = 1 := by
        have heq : 2 + (2 * h - 1) = 1 + 2 * h := by omega
        rw [heq, Nat.add_mod_right]
        apply Nat.mod_eq_of_lt
        omega
      first | rfl | exact h1 | exact h2 | exact h3
    have hact : activeB2 h x (pred2c h hh (state_y1 h hh x)) := by
      unfold activeB2
      rw [if_neg hm0_neg]
      left
      constructor
      · exact hx1
      · rw [h_pred, ha]
        change 1 ≤ 1 ∧ 1 ≤ h - 1
        constructor
        · exact Nat.le_refl _
        · omega
    unfold row_map
    rw [if_neg hy_neq, if_pos hact]
    unfold state_y2
    rw [h_pred]

  · -- Case 3: x.val = h + 4, h % 2 = 0
    have hx_neq : x.val ≠ h + 1 := by omega
    have ha : a_act h hh x = ⟨h - 3, by omega⟩ := by
      unfold a_act
      rw [if_neg hx_neq]
    have hs1 : state_y1 h hh x = ⟨h - 2, by omega⟩ := by
      unfold state_y1 succ2c one2
      rw [ha]
      ext
      change (h - 3 + 1) % (2 * h) = h - 2
      have h1 : h - 3 + 1 = h - 2 := by omega
      rw [h1]
      have h_lt : h - 2 < 2 * h := by omega
      exact Nat.mod_eq_of_lt h_lt
    have hy2 : ¬ y2SwitchRow h x := by unfold y2SwitchRow; omega
    have hj : jump_y h hh x = ⟨h - 3, by omega⟩ := by
      unfold jump_y A2 y2star succ2c one2
      rw [if_neg hy2]
      ext
      have hx_val : x.val = h + 4 := hx4
      change (((2 * h - 1 - x.val) + 1) % (2 * h) + 1) % (2 * h) = h - 3
      rw [hx_val]
      have h1 : 2 * h - 1 - (h + 4) = h - 5 := by omega
      rw [h1]
      have h2 : h - 5 + 1 = h - 4 := by omega
      rw [h2]
      have h_lt1 : h - 4 < 2 * h := by omega
      rw [Nat.mod_eq_of_lt h_lt1]
      have h3 : h - 4 + 1 = h - 3 := by omega
      rw [h3]
      have h_lt2 : h - 3 < 2 * h := by omega
      exact Nat.mod_eq_of_lt h_lt2
    have hy_neq : state_y1 h hh x ≠ jump_y h hh x := by
      rw [hs1, hj]
      intro h_eq
      have h_eq_val : h - 2 = h - 3 := congrArg Fin.val h_eq
      omega
    have h_pred : pred2c h hh (state_y1 h hh x) = a_act h hh x := by
      rw [hs1, ha]
      unfold pred2c one2
      ext
      have h1 : (2 * h - 1 + (h - 2)) % (2 * h) = h - 3 := by
        have heq : 2 * h - 1 + (h - 2) = h - 3 + 2 * h := by omega
        rw [heq, Nat.add_mod_right]
        apply Nat.mod_eq_of_lt
        omega
      have h2 : (h - 2 + (2 * h - 1) % (2 * h)) % (2 * h) = h - 3 := by
        have h_mod : (2 * h - 1) % (2 * h) = 2 * h - 1 := by apply Nat.mod_eq_of_lt; omega
        rw [h_mod]
        have heq : h - 2 + (2 * h - 1) = h - 3 + 2 * h := by omega
        rw [heq, Nat.add_mod_right]
        apply Nat.mod_eq_of_lt
        omega
      have h3 : (h - 2 + (2 * h - 1)) % (2 * h) = h - 3 := by
        have heq : h - 2 + (2 * h - 1) = h - 3 + 2 * h := by omega
        rw [heq, Nat.add_mod_right]
        apply Nat.mod_eq_of_lt
        omega
      first | rfl | exact h1 | exact h2 | exact h3
    have hact : activeB2 h x (pred2c h hh (state_y1 h hh x)) := by
      unfold activeB2
      rw [if_pos hm0]
      right
      constructor
      · exact hx4
      · rw [h_pred, ha]
        change h - 3 ≤ h - 3 ∧ h - 3 ≤ 2 * h - 2
        constructor
        · exact Nat.le_refl _
        · omega
    unfold row_map
    rw [if_neg hy_neq, if_pos hact]
    unfold state_y2
    rw [h_pred]

  · -- Case 4: x.val = h + 4, h % 2 = 1
    have hm0_neg : ¬ (h % 2 = 0) := by omega
    have hx_neq : x.val ≠ h + 1 := by omega
    have ha : a_act h hh x = ⟨h - 3, by omega⟩ := by
      unfold a_act
      rw [if_neg hx_neq]
    have hs1 : state_y1 h hh x = ⟨h - 2, by omega⟩ := by
      unfold state_y1 succ2c one2
      rw [ha]
      ext
      change (h - 3 + 1) % (2 * h) = h - 2
      have h1 : h - 3 + 1 = h - 2 := by omega
      rw [h1]
      have h_lt : h - 2 < 2 * h := by omega
      exact Nat.mod_eq_of_lt h_lt
    have hy2 : ¬ y2SwitchRow h x := by unfold y2SwitchRow; omega
    have hj : jump_y h hh x = ⟨h - 3, by omega⟩ := by
      unfold jump_y A2 y2star succ2c one2
      rw [if_neg hy2]
      ext
      have hx_val : x.val = h + 4 := hx4
      change (((2 * h - 1 - x.val) + 1) % (2 * h) + 1) % (2 * h) = h - 3
      rw [hx_val]
      have h1 : 2 * h - 1 - (h + 4) = h - 5 := by omega
      rw [h1]
      have h2 : h - 5 + 1 = h - 4 := by omega
      rw [h2]
      have h_lt1 : h - 4 < 2 * h := by omega
      rw [Nat.mod_eq_of_lt h_lt1]
      have h3 : h - 4 + 1 = h - 3 := by omega
      rw [h3]
      have h_lt2 : h - 3 < 2 * h := by omega
      exact Nat.mod_eq_of_lt h_lt2
    have hy_neq : state_y1 h hh x ≠ jump_y h hh x := by
      rw [hs1, hj]
      intro h_eq
      have h_eq_val : h - 2 = h - 3 := congrArg Fin.val h_eq
      omega
    have h_pred : pred2c h hh (state_y1 h hh x) = a_act h hh x := by
      rw [hs1, ha]
      unfold pred2c one2
      ext
      have h1 : (2 * h - 1 + (h - 2)) % (2 * h) = h - 3 := by
        have heq : 2 * h - 1 + (h - 2) = h - 3 + 2 * h := by omega
        rw [heq, Nat.add_mod_right]
        apply Nat.mod_eq_of_lt
        omega
      have h2 : (h - 2 + (2 * h - 1) % (2 * h)) % (2 * h) = h - 3 := by
        have h_mod : (2 * h - 1) % (2 * h) = 2 * h - 1 := by apply Nat.mod_eq_of_lt; omega
        rw [h_mod]
        have heq : h - 2 + (2 * h - 1) = h - 3 + 2 * h := by omega
        rw [heq, Nat.add_mod_right]
        apply Nat.mod_eq_of_lt
        omega
      have h3 : (h - 2 + (2 * h - 1)) % (2 * h) = h - 3 := by
        have heq : h - 2 + (2 * h - 1) = h - 3 + 2 * h := by omega
        rw [heq, Nat.add_mod_right]
        apply Nat.mod_eq_of_lt
        omega
      first | rfl | exact h1 | exact h2 | exact h3
    have hact : activeB2 h x (pred2c h hh (state_y1 h hh x)) := by
      unfold activeB2
      rw [if_neg hm0_neg]
      right
      constructor
      · exact hx4
      · rw [h_pred, ha]
    unfold row_map
    rw [if_neg hy_neq, if_pos hact]
    unfold state_y2
    rw [h_pred]

theorem iterate_eq_of_map_eq {α : Type} (f g : α → α) (x : α) (n : ℕ) (H : ∀ k < n, f (g^[k] x) = g (g^[k] x)) :
  f^[n] x = g^[n] x :=
by
  induction n with
  | zero => rfl
  | succ d ih =>
    have h1 : ∀ k < d, f (g^[k] x) = g (g^[k] x) := by
      intro k hk
      apply H
      omega
    have ih_d : f^[d] x = g^[d] x := ih h1
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih_d]
    apply H
    omega

theorem phase3_out_step (x : Fin (2 * h)) (h_act : ∃ y, activeB2 h x y) (k : ℕ) (hk : k < k_out h hh x) :
  row_map h hh x ((pred2c h hh)^[k] (state_y2 h hh x)) = pred2c h hh ((pred2c h hh)^[k] (state_y2 h hh x)) :=
by
  let y_k := (pred2c h hh)^[k] (state_y2 h hh x)
  change row_map h hh x y_k = pred2c h hh y_k

  have h_pred_zero : ∀ (v : Fin (2 * h)), v.val = 0 → (pred2c h hh v).val = 2 * h - 1 := by
    intro v hv
    unfold pred2c one2
    have h_sub := Fin.intCast_val_sub_eq_sub_add_ite v (⟨1, by omega⟩ : Fin (2 * h))
    split_ifs at h_sub with h_le
    · have h_le_val : (⟨1, by omega⟩ : Fin (2 * h)).val ≤ v.val := h_le
      have h_one : (⟨1, by omega⟩ : Fin (2 * h)).val = 1 := rfl
      rw [h_one] at h_le_val
      omega
    · change ((v - ⟨1, by omega⟩ : Fin (2 * h)).val : ℤ) = (v.val : ℤ) - ((⟨1, by omega⟩ : Fin (2 * h)).val : ℤ) + ((2 * h : ℕ) : ℤ) at h_sub
      have h_one_val : ((⟨1, by omega⟩ : Fin (2 * h)).val : ℤ) = 1 := rfl
      omega

  have h_pred_pos : ∀ (v : Fin (2 * h)), 0 < v.val → (pred2c h hh v).val = v.val - 1 := by
    intro v hv
    unfold pred2c one2
    have h_sub := Fin.intCast_val_sub_eq_sub_add_ite v (⟨1, by omega⟩ : Fin (2 * h))
    split_ifs at h_sub with h_le
    · change ((v - ⟨1, by omega⟩ : Fin (2 * h)).val : ℤ) = (v.val : ℤ) - ((⟨1, by omega⟩ : Fin (2 * h)).val : ℤ) + ((0 : ℕ) : ℤ) at h_sub
      have h_one_val : ((⟨1, by omega⟩ : Fin (2 * h)).val : ℤ) = 1 := rfl
      omega
    · have h_nle_val : ¬((⟨1, by omega⟩ : Fin (2 * h)).val ≤ v.val) := h_le
      have h_one : (⟨1, by omega⟩ : Fin (2 * h)).val = 1 := rfl
      rw [h_one] at h_nle_val
      omega

  have h_succ_lt : ∀ (v : Fin (2 * h)), v.val + 1 < 2 * h → (succ2c h hh v).val = v.val + 1 := by
    intro v hv
    unfold succ2c one2
    have h_def : (v + ⟨1, by omega⟩ : Fin (2 * h)).val = (v.val + 1) % (2 * h) := rfl
    rw [h_def]
    apply Nat.mod_eq_of_lt
    exact hv

  have h_succ_max : ∀ (v : Fin (2 * h)), v.val = 2 * h - 1 → (succ2c h hh v).val = 0 := by
    intro v hv
    unfold succ2c one2
    have h_def : (v + ⟨1, by omega⟩ : Fin (2 * h)).val = (v.val + 1) % (2 * h) := rfl
    rw [h_def, hv]
    have h1 : 2 * h - 1 + 1 = 2 * h := by omega
    rw [h1]
    exact Nat.mod_self (2 * h)

  obtain ⟨y_act, hy_act⟩ := h_act
  unfold activeB2 at hy_act
  split_ifs at hy_act with h_even
  · rcases hy_act with ⟨h1, _⟩ | ⟨h4, _, _⟩
    · -- Case 1: Even, x.val = h + 1
      have h_a_act : (a_act h hh x).val = 0 := by
        unfold a_act; rw [if_pos h1, if_pos h_even]
      have h_state_y2 : (state_y2 h hh x).val = 2 * h - 1 := by
        unfold state_y2
        exact h_pred_zero (a_act h hh x) h_a_act
      have h_L_act : L_act h hh x = h - 1 := by
        unfold L_act; rw [if_pos h1, if_pos h_even]
      have h_k_out : k_out h hh x = h - 1 := by
        unfold k_out; rw [h_L_act]; omega
      have h_k_out_lt : k < h - 1 := by omega

      have h_yk_val_lem : ∀ (j : ℕ), j < h - 1 → ((pred2c h hh)^[j] (state_y2 h hh x)).val = 2 * h - 1 - j := by
        intro j
        induction j with
        | zero =>
          intro _
          simp only [Function.iterate_zero, id_eq]
          have h_st := h_state_y2
          omega
        | succ j ih =>
          intro hj
          rw [Function.iterate_succ_apply']
          have hj_lt : j < h - 1 := by omega
          have ih2 := ih hj_lt
          have h_pos : 0 < ((pred2c h hh)^[j] (state_y2 h hh x)).val := by omega
          have h_pred := h_pred_pos _ h_pos
          omega
      have h_y_k : y_k.val = 2 * h - 1 - k := h_yk_val_lem k h_k_out_lt

      have h_y2Switch : y2SwitchRow h x := by
        unfold y2SwitchRow; omega
      have h_y2star : (y2star h hh x).val = 2 * h - 2 := by
        unfold y2star mMinusTwo2; rw [if_pos h_y2Switch, if_pos h_even]
      have h_A2 : (A2 h hh x).val = 2 * h - 1 := by
        unfold A2
        have h_lt : (y2star h hh x).val + 1 < 2 * h := by omega
        have h_succ := h_succ_lt (y2star h hh x) h_lt
        omega
      have h_jump : (jump_y h hh x).val = 0 := by
        unfold jump_y
        exact h_succ_max (A2 h hh x) h_A2

      have hyk_neq : y_k ≠ jump_y h hh x := by
        intro contra
        have h_val : y_k.val = (jump_y h hh x).val := by rw [contra]
        omega

      have h_not_active : ¬ activeB2 h x (pred2c h hh y_k) := by
        unfold activeB2; rw [if_pos h_even]
        intro h_act_cond
        have h_pos : 0 < y_k.val := by omega
        have h_pred_val := h_pred_pos y_k h_pos
        rw [h_pred_val] at h_act_cond
        rcases h_act_cond with ⟨_, _⟩ | ⟨_, _, _⟩ <;> omega

      unfold row_map
      rw [if_neg hyk_neq, if_neg h_not_active]

    · -- Case 2: Even, x.val = h + 4
      have h1_ne : x.val ≠ h + 1 := by omega
      have h_a_act : (a_act h hh x).val = h - 3 := by
        unfold a_act; rw [if_neg h1_ne]
      have h_state_y2 : (state_y2 h hh x).val = h - 4 := by
        unfold state_y2
        have h_pos : 0 < (a_act h hh x).val := by omega
        have h_pred := h_pred_pos (a_act h hh x) h_pos
        omega
      have h_L_act : L_act h hh x = h + 1 := by
        unfold L_act; rw [if_neg h1_ne, if_pos h_even]
      have h_k_out : k_out h hh x = h - 3 := by
        unfold k_out; rw [h_L_act]; omega
      have h_k_out_lt : k < h - 3 := by omega

      have h_yk_val_lem : ∀ (j : ℕ), j < h - 3 → ((pred2c h hh)^[j] (state_y2 h hh x)).val = h - 4 - j := by
        intro j
        induction j with
        | zero =>
          intro _
          simp only [Function.iterate_zero, id_eq]
          have h_st := h_state_y2
          omega
        | succ j ih =>
          intro hj
          rw [Function.iterate_succ_apply']
          have hj_lt : j < h - 3 := by omega
          have ih2 := ih hj_lt
          have h_pos : 0 < ((pred2c h hh)^[j] (state_y2 h hh x)).val := by omega
          have h_pred := h_pred_pos _ h_pos
          omega
      have h_y_k : y_k.val = h - 4 - k := h_yk_val_lem k h_k_out_lt

      have h_y2Switch : ¬ y2SwitchRow h x := by
        unfold y2SwitchRow; omega
      have h_y2star : (y2star h hh x).val = h - 5 := by
        unfold y2star; rw [if_neg h_y2Switch]
        change 2 * h - 1 - x.val = h - 5
        omega
      have h_A2 : (A2 h hh x).val = h - 4 := by
        unfold A2
        have h_lt : (y2star h hh x).val + 1 < 2 * h := by omega
        have h_succ := h_succ_lt (y2star h hh x) h_lt
        omega
      have h_jump : (jump_y h hh x).val = h - 3 := by
        unfold jump_y
        have h_lt : (A2 h hh x).val + 1 < 2 * h := by omega
        have h_succ := h_succ_lt (A2 h hh x) h_lt
        omega

      have hyk_neq : y_k ≠ jump_y h hh x := by
        intro contra
        have h_val : y_k.val = (jump_y h hh x).val := by rw [contra]
        omega

      have h_not_active : ¬ activeB2 h x (pred2c h hh y_k) := by
        unfold activeB2; rw [if_pos h_even]
        intro h_act_cond
        rcases eq_or_lt_of_le (show k ≤ h - 4 by omega) with rfl | hk_lt
        · have h_yk_zero : y_k.val = 0 := by omega
          have h_pred_val := h_pred_zero y_k h_yk_zero
          rw [h_pred_val] at h_act_cond
          rcases h_act_cond with ⟨_, _⟩ | ⟨_, _, _⟩ <;> omega
        · have h_pos : 0 < y_k.val := by omega
          have h_pred_val := h_pred_pos y_k h_pos
          rw [h_pred_val] at h_act_cond
          rcases h_act_cond with ⟨_, _⟩ | ⟨_, _, _⟩ <;> omega

      unfold row_map
      rw [if_neg hyk_neq, if_neg h_not_active]

  · rcases hy_act with ⟨h1, _, _⟩ | ⟨h4, _⟩
    · -- Case 3: Odd, x.val = h + 1
      have h_ne_0 : h % 2 ≠ 0 := h_even
      have h_a_act : (a_act h hh x).val = 1 := by
        unfold a_act; rw [if_pos h1, if_neg h_ne_0]
      have h_state_y2 : (state_y2 h hh x).val = 0 := by
        unfold state_y2
        have h_pos : 0 < (a_act h hh x).val := by omega
        have h_pred := h_pred_pos (a_act h hh x) h_pos
        omega
      have h_L_act : L_act h hh x = h - 2 := by
        unfold L_act; rw [if_pos h1, if_neg h_ne_0]
      have h_k_out : k_out h hh x = h := by
        unfold k_out; rw [h_L_act]; omega
      have h_k_out_lt : k < h := by omega

      have h_yk_val_lem : ∀ (j : ℕ), j < h → j > 0 → ((pred2c h hh)^[j] (state_y2 h hh x)).val = 2 * h - j := by
        intro j
        induction j with
        | zero => intro _ hj_pos; omega
        | succ j ih =>
          intro hj _
          rw [Function.iterate_succ_apply']
          rcases Nat.eq_zero_or_pos j with rfl | hj_pos
          · simp only [Function.iterate_zero, id_eq]
            have h_st := h_state_y2
            have h_pred := h_pred_zero _ h_st
            omega
          · have hj_lt : j < h := by omega
            have ih2 := ih hj_lt hj_pos
            have h_pos : 0 < ((pred2c h hh)^[j] (state_y2 h hh x)).val := by omega
            have h_pred := h_pred_pos _ h_pos
            omega

      have h_y_k_cases : k = 0 ∨ (k > 0 ∧ y_k.val = 2 * h - k) := by
        rcases Nat.eq_zero_or_pos k with rfl | hk_pos
        · left; rfl
        · right; exact ⟨hk_pos, h_yk_val_lem k h_k_out_lt hk_pos⟩

      have h_y2Switch : y2SwitchRow h x := by
        unfold y2SwitchRow; omega
      have h_y2star : (y2star h hh x).val = 2 * h - 1 := by
        unfold y2star mMinusOne2; rw [if_pos h_y2Switch, if_neg h_ne_0]
      have h_A2 : (A2 h hh x).val = 0 := by
        unfold A2
        exact h_succ_max (y2star h hh x) h_y2star
      have h_jump : (jump_y h hh x).val = 1 := by
        unfold jump_y
        have h_lt : (A2 h hh x).val + 1 < 2 * h := by omega
        have h_succ := h_succ_lt (A2 h hh x) h_lt
        omega

      have hyk_neq : y_k ≠ jump_y h hh x := by
        intro contra
        have h_val : y_k.val = (jump_y h hh x).val := by rw [contra]
        rcases h_y_k_cases with rfl | ⟨_, hyk⟩
        · simp only [y_k, Function.iterate_zero, id_eq] at h_val
          have h_st := h_state_y2
          omega
        · omega

      have h_not_active : ¬ activeB2 h x (pred2c h hh y_k) := by
        unfold activeB2; rw [if_neg h_ne_0]
        intro h_act_cond
        rcases h_y_k_cases with rfl | ⟨_, hyk⟩
        · have h_yk_zero : y_k.val = 0 := h_state_y2
          have h_pred_val := h_pred_zero y_k h_yk_zero
          rw [h_pred_val] at h_act_cond
          rcases h_act_cond with ⟨_, _, _⟩ | ⟨_, _⟩ <;> omega
        · have h_pos : 0 < y_k.val := by omega
          have h_pred_val := h_pred_pos y_k h_pos
          rw [h_pred_val] at h_act_cond
          rcases h_act_cond with ⟨_, _, _⟩ | ⟨_, _⟩ <;> omega

      unfold row_map
      rw [if_neg hyk_neq, if_neg h_not_active]

    · -- Case 4: Odd, x.val = h + 4
      have h_ne_0 : h % 2 ≠ 0 := h_even
      have h1_ne : x.val ≠ h + 1 := by omega
      have h_a_act : (a_act h hh x).val = h - 3 := by
        unfold a_act; rw [if_neg h1_ne]
      have h_state_y2 : (state_y2 h hh x).val = h - 4 := by
        unfold state_y2
        have h_pos : 0 < (a_act h hh x).val := by omega
        have h_pred := h_pred_pos (a_act h hh x) h_pos
        omega
      have h_L_act : L_act h hh x = h + 2 := by
        unfold L_act; rw [if_neg h1_ne, if_neg h_ne_0]
      have h_k_out : k_out h hh x = h - 4 := by
        unfold k_out; rw [h_L_act]; omega
      have h_k_out_lt : k < h - 4 := by omega

      have h_yk_val_lem : ∀ (j : ℕ), j < h - 4 → ((pred2c h hh)^[j] (state_y2 h hh x)).val = h - 4 - j := by
        intro j
        induction j with
        | zero =>
          intro _
          simp only [Function.iterate_zero, id_eq]
          have h_st := h_state_y2
          omega
        | succ j ih =>
          intro hj
          rw [Function.iterate_succ_apply']
          have hj_lt : j < h - 4 := by omega
          have ih2 := ih hj_lt
          have h_pos : 0 < ((pred2c h hh)^[j] (state_y2 h hh x)).val := by omega
          have h_pred := h_pred_pos _ h_pos
          omega
      have h_y_k : y_k.val = h - 4 - k := h_yk_val_lem k h_k_out_lt

      have h_y2Switch : ¬ y2SwitchRow h x := by
        unfold y2SwitchRow; omega
      have h_y2star : (y2star h hh x).val = h - 5 := by
        unfold y2star
        rw [if_neg h_y2Switch]
        change 2 * h - 1 - x.val = h - 5
        omega
      have h_A2 : (A2 h hh x).val = h - 4 := by
        unfold A2
        have h_lt : (y2star h hh x).val + 1 < 2 * h := by omega
        have h_succ := h_succ_lt (y2star h hh x) h_lt
        omega
      have h_jump : (jump_y h hh x).val = h - 3 := by
        unfold jump_y
        have h_lt : (A2 h hh x).val + 1 < 2 * h := by omega
        have h_succ := h_succ_lt (A2 h hh x) h_lt
        omega

      have hyk_neq : y_k ≠ jump_y h hh x := by
        intro contra
        have h_val : y_k.val = (jump_y h hh x).val := by rw [contra]
        omega

      have h_not_active : ¬ activeB2 h x (pred2c h hh y_k) := by
        unfold activeB2; rw [if_neg h_ne_0]
        intro h_act_cond
        have h_pos : 0 < y_k.val := by omega
        have h_pred_val := h_pred_pos y_k h_pos
        rw [h_pred_val] at h_act_cond
        rcases h_act_cond with ⟨_, _, _⟩ | ⟨_, _⟩ <;> omega

      unfold row_map
      rw [if_neg hyk_neq, if_neg h_not_active]

theorem activeB2_cases (h : ℕ) (hh : 5 ≤ h) (x : Fin (2 * h)) (h_act : ∃ y, activeB2 h x y) :
  x.val = h + 1 ∨ x.val = h + 4 :=
by
  rcases h_act with ⟨y, hy⟩
  unfold activeB2 at hy
  split_ifs at hy
  · rcases hy with ⟨h1, _⟩ | ⟨h4, _⟩
    · left
      exact h1
    · right
      exact h4
  · rcases hy with ⟨h1, _⟩ | ⟨h4, _⟩
    · left
      exact h1
    · right
      exact h4

theorem phase3_out_end_case1 (h : ℕ) (hh : 5 ≤ h) (x : Fin (2 * h)) (hx : x.val = h + 1) (h_mod : h % 2 = 0) :
  (pred2c h hh)^[k_out h hh x] (state_y2 h hh x) = state_y3 h hh x :=
by
  haveI : NeZero (2 * h) := ⟨by omega⟩

  have one2_eq_one : one2 h hh = 1 := by
    apply Fin.ext
    exact (Nat.mod_eq_of_lt (by omega)).symm

  have natToFin_zero : natToFin h hh 0 = 0 := by
    apply Fin.ext
    exact Nat.zero_mod (2 * h)

  have natToFin_succ : ∀ k, natToFin h hh (k + 1) = natToFin h hh k + 1 := by
    intro k
    apply Fin.ext
    exact Nat.add_mod k 1 (2 * h)

  have natToFin_add : ∀ a b, natToFin h hh (a + b) = natToFin h hh a + natToFin h hh b := by
    intro a b
    apply Fin.ext
    exact Nat.add_mod a b (2 * h)

  have pred2c_iterate_eq : ∀ (k : ℕ) (y : Fin (2 * h)), (pred2c h hh)^[k] y = y - natToFin h hh k := by
    intro k
    induction k with
    | zero =>
      intro y
      rw [Function.iterate_zero_apply]
      rw [natToFin_zero, sub_zero]
    | succ k ih =>
      intro y
      have h_iter : (pred2c h hh)^[k + 1] y = (pred2c h hh)^[k] (pred2c h hh y) := rfl
      rw [h_iter]
      rw [ih (pred2c h hh y)]
      unfold pred2c
      rw [one2_eq_one]
      rw [natToFin_succ]
      rw [sub_sub]
      rw [add_comm 1 (natToFin h hh k)]

  have h_a : a_act h hh x = 0 := by
    apply Fin.ext
    unfold a_act
    rw [if_pos hx, if_pos h_mod]
    exact (Nat.zero_mod (2 * h)).symm

  have h_y2 : state_y2 h hh x = -1 := by
    unfold state_y2
    rw [h_a]
    unfold pred2c
    rw [one2_eq_one]
    rw [zero_sub]

  have h_k_nat : k_out h hh x = h - 1 := by
    unfold k_out L_act
    rw [if_pos hx, if_pos h_mod]
    omega

  have h_b : b_act h hh x = natToFin h hh (h - 1) := by
    apply Fin.ext
    unfold b_act
    rw [if_pos hx]
    exact (Nat.mod_eq_of_lt (by omega)).symm

  have h_y3 : state_y3 h hh x = natToFin h hh h := by
    unfold state_y3
    have succ2c_eq : ∀ y, succ2c h hh y = y + 1 := by
      intro y; unfold succ2c; rw [one2_eq_one]
    rw [succ2c_eq]
    rw [h_b]
    have H : natToFin h hh h = natToFin h hh (h - 1) + 1 := by
      have h_eq : h - 1 + 1 = h := by omega
      have step := natToFin_succ (h - 1)
      rw [h_eq] at step
      exact step
    exact H.symm

  rw [h_k_nat]
  rw [pred2c_iterate_eq]
  rw [h_y2]
  rw [h_y3]

  have H_add : natToFin h hh h + natToFin h hh h = 0 := by
    have H_2h : natToFin h hh (2 * h) = 0 := by
      apply Fin.ext
      exact Eq.trans (Nat.mod_self (2 * h)) (Nat.zero_mod (2 * h)).symm
    have H_2h_split : natToFin h hh (2 * h) = natToFin h hh h + natToFin h hh h := by
      have h_eq : h + h = 2 * h := by omega
      have step := natToFin_add h h
      rw [h_eq] at step
      exact step
    rw [H_2h_split] at H_2h
    exact H_2h

  have neg_one_eq : (-1 : Fin (2 * h)) = 0 - 1 := by rw [zero_sub]

  calc (-1 : Fin (2 * h)) - natToFin h hh (h - 1)
    _ = (0 - 1 : Fin (2 * h)) - natToFin h hh (h - 1) := by rw [neg_one_eq]
    _ = (natToFin h hh h + natToFin h hh h - 1) - natToFin h hh (h - 1) := by rw [← H_add]
    _ = (natToFin h hh h + (natToFin h hh h - 1)) - natToFin h hh (h - 1) := by rw [add_sub_assoc]
    _ = natToFin h hh h + (natToFin h hh h - 1 - natToFin h hh (h - 1)) := by rw [add_sub_assoc]
    _ = natToFin h hh h + 0 := by
      have H_cast : natToFin h hh h - 1 = natToFin h hh (h - 1) := by
        have H : natToFin h hh h = natToFin h hh (h - 1) + 1 := by
          have h_eq : h - 1 + 1 = h := by omega
          have step := natToFin_succ (h - 1)
          rw [h_eq] at step
          exact step
        rw [H]
        rw [add_sub_assoc]
        rw [sub_self]
        rw [add_zero]
      rw [H_cast]
      rw [sub_self]
    _ = natToFin h hh h := by rw [add_zero]

theorem phase3_out_end_case2 (h : ℕ) (hh : 5 ≤ h) (x : Fin (2 * h)) (hx : x.val = h + 1) (h_mod : ¬ (h % 2 = 0)) :
  (pred2c h hh)^[k_out h hh x] (state_y2 h hh x) = state_y3 h hh x :=
by
  have _inst : NeZero (2 * h) := ⟨by omega⟩
  let toFin : ℕ → Fin (2 * h) := fun k => ⟨k % (2 * h), by
    have : 0 < 2 * h := by omega
    exact Nat.mod_lt k this
  ⟩

  have h_one2 : one2 h hh = (1 : Fin (2 * h)) := by
    unfold one2
    apply Fin.ext
    change 1 = (1 : Fin (2 * h)).val
    have h_one_val : (1 : Fin (2 * h)).val = 1 := by
      change 1 % (2 * h) = 1
      exact Nat.mod_eq_of_lt (by omega)
    rw [h_one_val]

  have h_pred2c : ∀ y, pred2c h hh y = y - (1 : Fin (2 * h)) := by
    intro y
    unfold pred2c
    rw [h_one2]

  have h_iter : ∀ (k : ℕ) (y : Fin (2 * h)), (pred2c h hh)^[k] y = y - toFin k := by
    intro k
    induction k with
    | zero =>
      intro y
      have h0 : toFin 0 = (0 : Fin (2 * h)) := by
        apply Fin.ext
        change 0 % (2 * h) = (0 : Fin (2 * h)).val
        have h_zero_val : (0 : Fin (2 * h)).val = 0 := by
          change 0 % (2 * h) = 0
          exact Nat.zero_mod (2 * h)
        rw [h_zero_val]
        exact Nat.zero_mod (2 * h)
      rw [h0]
      rw [sub_zero]
      exact rfl
    | succ k ih =>
      intro y
      have h_step : (pred2c h hh)^[k + 1] y = (pred2c h hh)^[k] (pred2c h hh y) := rfl
      rw [h_step]
      rw [ih (pred2c h hh y)]
      rw [h_pred2c y]
      have hc : toFin (k + 1) = toFin k + (1 : Fin (2 * h)) := by
        apply Fin.ext
        change (k + 1) % (2 * h) = ((toFin k).val + (1 : Fin (2 * h)).val) % (2 * h)
        have h1_val : (1 : Fin (2 * h)).val = 1 := by
          change 1 % (2 * h) = 1
          exact Nat.mod_eq_of_lt (by omega)
        have hk_val : (toFin k).val = k % (2 * h) := rfl
        rw [h1_val, hk_val]
        have H_add : (k + 1) % (2 * h) = (k % (2 * h) + 1 % (2 * h)) % (2 * h) := Nat.add_mod k 1 (2 * h)
        have H_one : 1 % (2 * h) = 1 := Nat.mod_eq_of_lt (by omega)
        rw [H_one] at H_add
        exact H_add
      rw [hc]
      rw [sub_sub]
      rw [add_comm (1 : Fin (2 * h)) (toFin k)]

  have ha : a_act h hh x = (1 : Fin (2 * h)) := by
    unfold a_act
    have h1 : x.val = h + 1 := hx
    have h2 : ¬ (h % 2 = 0) := h_mod
    simp [h1, h2]
    apply Fin.ext
    change 1 = (1 : Fin (2 * h)).val
    have h_one_val : (1 : Fin (2 * h)).val = 1 := by
      change 1 % (2 * h) = 1
      exact Nat.mod_eq_of_lt (by omega)
    rw [h_one_val]

  have hb : b_act h hh x = ⟨h - 1, by omega⟩ := by
    unfold b_act
    have h1 : x.val = h + 1 := hx
    simp [h1]

  have hy2 : state_y2 h hh x = (0 : Fin (2 * h)) := by
    unfold state_y2
    rw [ha, h_pred2c (1 : Fin (2 * h))]
    exact sub_self (1 : Fin (2 * h))

  have hy3 : state_y3 h hh x = toFin h := by
    unfold state_y3 succ2c
    rw [hb, h_one2]
    apply Fin.ext
    change ((h - 1) + (1 : Fin (2 * h)).val) % (2 * h) = (toFin h).val
    have h_one_val : (1 : Fin (2 * h)).val = 1 := by
      change 1 % (2 * h) = 1
      exact Nat.mod_eq_of_lt (by omega)
    rw [h_one_val]
    have h_h_val : (toFin h).val = h % (2 * h) := rfl
    rw [h_h_val]
    have h_eq : h - 1 + 1 = h := by omega
    rw [h_eq]

  have hk : k_out h hh x = h := by
    unfold k_out L_act
    have h1 : x.val = h + 1 := hx
    have h2 : ¬ (h % 2 = 0) := h_mod
    simp [h1, h2]
    omega

  have h_zero : toFin h + toFin h = (0 : Fin (2 * h)) := by
    apply Fin.ext
    change ((toFin h).val + (toFin h).val) % (2 * h) = (0 : Fin (2 * h)).val
    have h_h_val : (toFin h).val = h % (2 * h) := rfl
    rw [h_h_val]
    have h_mod_h : h % (2 * h) = h := Nat.mod_eq_of_lt (by omega)
    rw [h_mod_h]
    have h_zero_val : (0 : Fin (2 * h)).val = 0 := by
      change 0 % (2 * h) = 0
      exact Nat.zero_mod (2 * h)
    rw [h_zero_val]
    have h_eq : h + h = 2 * h := by omega
    rw [h_eq]
    exact Nat.mod_self (2 * h)

  rw [hk, hy2, hy3]
  rw [h_iter h (0 : Fin (2 * h))]

  have h_end : (0 : Fin (2 * h)) - toFin h = toFin h := by
    rw [← h_zero]
    rw [add_sub_assoc]
    rw [sub_self]
    rw [add_zero]

  exact h_end

theorem state_y2_val_case3 (h : ℕ) (hh : 5 ≤ h) (x : Fin (2 * h)) (hx : x.val = h + 4) (h_mod : h % 2 = 0) :
  (state_y2 h hh x).val = h - 4 :=
by
  have h1 : ¬(x.val = h + 1) := by omega
  have h_a_act : a_act h hh x = ⟨h - 3, by omega⟩ := by
    unfold a_act
    simp [h1]
  unfold state_y2 pred2c one2
  rw [h_a_act]
  have H := Fin.intCast_val_sub_eq_sub_add_ite (⟨h - 3, by omega⟩ : Fin (2 * h)) (⟨1, by omega⟩ : Fin (2 * h))
  have eq_a : (⟨h - 3, by omega⟩ : Fin (2 * h)).val = h - 3 := rfl
  have eq_b : (⟨1, by omega⟩ : Fin (2 * h)).val = 1 := rfl
  split_ifs at H
  · rw [eq_a, eq_b] at H
    zify
    omega
  · omega

theorem state_y3_val_case3 (h : ℕ) (hh : 5 ≤ h) (x : Fin (2 * h)) (hx : x.val = h + 4) (h_mod : h % 2 = 0) :
  (state_y3 h hh x).val = 2 * h - 1 :=
by
  simp only [state_y3, succ2c, b_act, one2]
  split_ifs
  · omega
  · change (2 * h - 2 + 1) % (2 * h) = 2 * h - 1
    have h_eq : 2 * h - 2 + 1 = 2 * h - 1 := by omega
    rw [h_eq]
    apply Nat.mod_eq_of_lt
    omega

theorem L_act_val_case3 (h : ℕ) (hh : 5 ≤ h) (x : Fin (2 * h)) (hx : x.val = h + 4) (h_mod : h % 2 = 0) :
  L_act h hh x = h + 1 :=
by
  unfold L_act
  have h_neq : x.val ≠ h + 1 := by omega
  simp [h_neq, h_mod]

theorem k_out_val_case3 (h : ℕ) (hh : 5 ≤ h) (x : Fin (2 * h)) (hx : x.val = h + 4) (h_mod : h % 2 = 0) :
  k_out h hh x = h - 3 :=
by
  unfold k_out
  rw [L_act_val_case3 h hh x hx h_mod]
  omega

theorem pred2c_iterate_eq (y : Fin (2 * h)) (k : ℕ) :
  (pred2c h hh)^[k] y = y - ⟨k % (2 * h), by apply Nat.mod_lt; omega⟩ :=
by
  have _inst : NeZero (2 * h) := ⟨by omega⟩
  induction k with
  | zero =>
    rw [Function.iterate_zero]
    have hz : (⟨0 % (2 * h), by apply Nat.mod_lt; omega⟩ : Fin (2 * h)) = 0 := by
      ext
      exact Nat.zero_mod (2 * h)
    rw [hz, sub_zero]
    rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih]
    unfold pred2c one2
    have h_succ : (⟨(k + 1) % (2 * h), by apply Nat.mod_lt; omega⟩ : Fin (2 * h)) =
                  (⟨k % (2 * h), by apply Nat.mod_lt; omega⟩ : Fin (2 * h)) + ⟨1, by omega⟩ := by
      ext
      change (k + 1) % (2 * h) = (k % (2 * h) + 1) % (2 * h)
      have h1 : 1 % (2 * h) = 1 := by apply Nat.mod_eq_of_lt; omega
      have h2 : (k % (2 * h) + 1) % (2 * h) = (k % (2 * h) + 1 % (2 * h)) % (2 * h) := by rw [h1]
      rw [h2, ← Nat.add_mod]
    rw [h_succ, sub_add_eq_sub_sub]

theorem fin_sub_val {n : ℕ} (a b : Fin n) :
  (a - b).val = (a.val + n - b.val) % n :=
by
  have h := Fin.coe_int_sub_eq_ite a b
  have ha := a.isLt
  have hb := b.isLt
  by_cases hba : b ≤ a
  · have hba_val : b.val ≤ a.val := hba
    rw [if_pos hba] at h
    have h2 : a.val + n - b.val = a.val - b.val + n := by omega
    rw [h2, Nat.add_mod_right]
    have h3 : (a.val - b.val) % n = a.val - b.val := by
      apply Nat.mod_eq_of_lt
      omega
    rw [h3]
    omega
  · have hba_val : ¬ (b.val ≤ a.val) := hba
    rw [if_neg hba] at h
    have h3 : (a.val + n - b.val) % n = a.val + n - b.val := by
      apply Nat.mod_eq_of_lt
      omega
    rw [h3]
    omega

theorem phase3_out_end_case3 (h : ℕ) (hh : 5 ≤ h) (x : Fin (2 * h)) (hx : x.val = h + 4) (h_mod : h % 2 = 0) :
  (pred2c h hh)^[k_out h hh x] (state_y2 h hh x) = state_y3 h hh x :=
by
  have h2 := state_y2_val_case3 h hh x hx h_mod
  have h3 := state_y3_val_case3 h hh x hx h_mod
  have hk := k_out_val_case3 h hh x hx h_mod
  rw [pred2c_iterate_eq]
  apply Fin.ext
  rw [fin_sub_val]
  rw [h2, h3]
  change (h - 4 + 2 * h - k_out h hh x % (2 * h)) % (2 * h) = 2 * h - 1
  rw [hk]
  have step2 : (h - 3) % (2 * h) = h - 3 := by
    exact Nat.mod_eq_of_lt (by omega)
  rw [step2]
  have step3 : (h - 4 + 2 * h - (h - 3)) = 2 * h - 1 := by omega
  rw [step3]
  have step4 : (2 * h - 1) % (2 * h) = 2 * h - 1 := by
    exact Nat.mod_eq_of_lt (by omega)
  rw [step4]

theorem phase3_out_end_case4 (h : ℕ) (hh : 5 ≤ h) (x : Fin (2 * h)) (hx : x.val = h + 4) (h_mod : ¬ (h % 2 = 0)) :
  (pred2c h hh)^[k_out h hh x] (state_y2 h hh x) = state_y3 h hh x :=
by
  have h1 : ¬ (x.val = h + 1) := by omega
  have h2 : ¬ (h % 2 = 0) := h_mod

  have ha : a_act h hh x = ⟨h - 3, by omega⟩ := by
    apply Fin.ext
    unfold a_act
    simp [h1]

  have hb : b_act h hh x = ⟨2 * h - 1, by omega⟩ := by
    apply Fin.ext
    unfold b_act
    simp [h1, h2]

  have hL : L_act h hh x = h + 2 := by
    unfold L_act
    simp [h1, h2]

  have hk_val : k_out h hh x = h - 4 := by
    unfold k_out
    rw [hL]
    omega

  haveI : NeZero (2 * h) := ⟨by omega⟩

  have H_pred : ∀ (y : Fin (2 * h)), y.val ≥ 1 → (pred2c h hh y).val = y.val - 1 := by
    intro y hy
    unfold pred2c
    have H_one : one2 h hh = 1 := by
      apply Fin.ext
      first | rfl | (change 1 = 1 % (2 * h); exact (Nat.mod_eq_of_lt (by omega)).symm)
    rw [H_one]
    have y_ne_zero : y ≠ 0 := by
      intro h_eq
      have h_eq_val : y.val = 0 := by
        rw [h_eq]
        first | rfl | (change 0 % (2 * h) = 0; exact Nat.zero_mod _)
      omega
    exact Fin.val_sub_one_of_ne_zero y_ne_zero

  have hy2_eq : state_y2 h hh x = ⟨h - 4, by omega⟩ := by
    unfold state_y2
    rw [ha]
    apply Fin.ext
    have H_ge : (⟨h - 3, by omega⟩ : Fin (2 * h)).val ≥ 1 := by
      change h - 3 ≥ 1
      omega
    have H_step := H_pred ⟨h - 3, by omega⟩ H_ge
    rw [H_step]
    change h - 3 - 1 = h - 4
    omega

  have hy3_eq : state_y3 h hh x = ⟨0, by omega⟩ := by
    unfold state_y3
    rw [hb]
    apply Fin.ext
    have h_val : (succ2c h hh ⟨2 * h - 1, by omega⟩).val = (2 * h - 1 + 1) % (2 * h) := by
      unfold succ2c one2
      rfl
    rw [h_val]
    have H_add : 2 * h - 1 + 1 = 2 * h := by omega
    rw [H_add]
    exact Nat.mod_self (2 * h)

  have H_iter : ∀ (k : ℕ), k ≤ h - 4 → ((pred2c h hh)^[k] ⟨h - 4, by omega⟩).val = h - 4 - k := by
    intro k
    induction k with
    | zero =>
      intro _
      change h - 4 = h - 4 - 0
      omega
    | succ k ih =>
      intro hk
      have hk_lt : k < h - 4 := by omega
      have ih_val : ((pred2c h hh)^[k] ⟨h - 4, by omega⟩).val = h - 4 - k := ih (by omega)
      rw [Function.iterate_succ_apply']
      have H_val_ge_1 : ((pred2c h hh)^[k] ⟨h - 4, by omega⟩).val ≥ 1 := by
        rw [ih_val]
        omega
      have H_step := H_pred ((pred2c h hh)^[k] ⟨h - 4, by omega⟩) H_val_ge_1
      rw [H_step]
      rw [ih_val]
      omega

  rw [hk_val, hy2_eq, hy3_eq]
  apply Fin.ext
  have H_final := H_iter (h - 4) (by omega)
  rw [H_final]
  change h - 4 - (h - 4) = 0
  omega

theorem phase3_out_end (x : Fin (2 * h)) (h_act : ∃ y, activeB2 h x y) :
  (pred2c h hh)^[k_out h hh x] (state_y2 h hh x) = state_y3 h hh x :=
by
  have h_cases := activeB2_cases h hh x h_act
  by_cases h_mod : h % 2 = 0
  · cases h_cases with
    | inl hx => exact phase3_out_end_case1 h hh x hx h_mod
    | inr hx => exact phase3_out_end_case3 h hh x hx h_mod
  · cases h_cases with
    | inl hx => exact phase3_out_end_case2 h hh x hx h_mod
    | inr hx => exact phase3_out_end_case4 h hh x hx h_mod

theorem phase3_out (x : Fin (2 * h)) (h_act : ∃ y, activeB2 h x y) :
  (row_map h hh x)^[k_out h hh x] (state_y2 h hh x) = state_y3 h hh x :=
by
  have H1 := iterate_eq_of_map_eq (row_map h hh x) (pred2c h hh) (state_y2 h hh x) (k_out h hh x) (phase3_out_step h hh x h_act)
  rw [H1]
  exact phase3_out_end h hh x h_act

theorem phase4_trans_in (x : Fin (2 * h)) (h_act : ∃ y, activeB2 h x y) :
  (row_map h hh x)^[k_trans_in h hh x] (state_y3 h hh x) = state_y4 h hh x :=
by
  change row_map h hh x (state_y3 h hh x) = state_y4 h hh x

  have hx : x.val = h + 1 ∨ x.val = h + 4 := by
    rcases h_act with ⟨y, hy⟩
    unfold activeB2 at hy
    split_ifs at hy with heven
    · rcases hy with ⟨h1, _⟩ | ⟨h4, _⟩
      · left; exact h1
      · right; exact h4
    · rcases hy with ⟨h1, _⟩ | ⟨h4, _⟩
      · left; exact h1
      · right; exact h4

  have pred_succ (z : Fin (2 * h)) : pred2c h hh (succ2c h hh z) = z := by
    unfold pred2c succ2c
    haveI : NeZero (2 * h) := ⟨by omega⟩
    exact add_sub_cancel_right z (one2 h hh)

  have h_pred_y3 : pred2c h hh (state_y3 h hh x) = b_act h hh x := by
    unfold state_y3
    exact pred_succ (b_act h hh x)

  have h_b_act_val :
    (b_act h hh x).val = if x.val = h + 1 then h - 1 else if h % 2 = 0 then 2 * h - 2 else 2 * h - 1 := by
    unfold b_act
    split_ifs <;> rfl

  have h_active : activeB2 h x (b_act h hh x) := by
    unfold activeB2
    rw [h_b_act_val]
    rcases hx with h1 | h4
    · split_ifs <;> (try left) <;> omega
    · split_ifs <;> (try right) <;> omega

  have h_succ2c_val : ∀ (z : Fin (2 * h)), z.val + 1 < 2 * h → (succ2c h hh z).val = z.val + 1 := by
    intro z hz
    unfold succ2c one2
    change (z.val + 1) % (2 * h) = z.val + 1
    exact Nat.mod_eq_of_lt hz

  have h_succ2c_val_max : ∀ (z : Fin (2 * h)), z.val = 2 * h - 1 → (succ2c h hh z).val = 0 := by
    intro z hz
    unfold succ2c one2
    change (z.val + 1) % (2 * h) = 0
    rw [hz]
    have : 2 * h - 1 + 1 = 2 * h := by omega
    rw [this]
    exact Nat.mod_self (2 * h)

  have h_not_jump : state_y3 h hh x ≠ jump_y h hh x := by
    intro heq
    have heq_val := congrArg Fin.val heq
    rcases hx with h1 | h4
    · have hb : (b_act h hh x).val = h - 1 := by
        unfold b_act
        rw [if_pos h1]
      have hy3 : (state_y3 h hh x).val = h := by
        unfold state_y3
        rw [h_succ2c_val]
        · omega
        · omega
      have hy2star : (y2star h hh x).val = if h % 2 = 0 then 2 * h - 2 else 2 * h - 1 := by
        unfold y2star y2SwitchRow mMinusTwo2 mMinusOne2
        have h_or : x.val = h + 1 ∨ x.val = h + 2 ∨ x.val = h + 3 := Or.inl h1
        rw [if_pos h_or]
        split_ifs <;> rfl
      by_cases heven : h % 2 = 0
      · have hy2s : (y2star h hh x).val = 2 * h - 2 := by rw [hy2star, if_pos heven]
        have hA2 : (A2 h hh x).val = 2 * h - 1 := by
          unfold A2
          rw [h_succ2c_val]
          · omega
          · omega
        have hjump : (jump_y h hh x).val = 0 := by
          unfold jump_y
          exact h_succ2c_val_max _ hA2
        omega
      · have hy2s : (y2star h hh x).val = 2 * h - 1 := by rw [hy2star, if_neg heven]
        have hA2 : (A2 h hh x).val = 0 := by
          unfold A2
          exact h_succ2c_val_max _ hy2s
        have hjump : (jump_y h hh x).val = 1 := by
          unfold jump_y
          rw [h_succ2c_val]
          · omega
          · omega
        omega
    · have h1_false : ¬(x.val = h + 1) := by omega
      have hb : (b_act h hh x).val = if h % 2 = 0 then 2 * h - 2 else 2 * h - 1 := by
        unfold b_act
        rw [if_neg h1_false]
        split_ifs <;> rfl
      by_cases heven : h % 2 = 0
      · have hb_even : (b_act h hh x).val = 2 * h - 2 := by rw [hb, if_pos heven]
        have hy3 : (state_y3 h hh x).val = 2 * h - 1 := by
          unfold state_y3
          rw [h_succ2c_val]
          · omega
          · omega
        have hy2star : (y2star h hh x).val = h - 5 := by
          unfold y2star y2SwitchRow
          have h_nor : ¬(x.val = h + 1 ∨ x.val = h + 2 ∨ x.val = h + 3) := by omega
          rw [if_neg h_nor]
          change 2 * h - 1 - x.val = h - 5
          omega
        have hA2 : (A2 h hh x).val = h - 4 := by
          unfold A2
          rw [h_succ2c_val]
          · omega
          · omega
        have hjump : (jump_y h hh x).val = h - 3 := by
          unfold jump_y
          rw [h_succ2c_val]
          · omega
          · omega
        omega
      · have hb_odd : (b_act h hh x).val = 2 * h - 1 := by rw [hb, if_neg heven]
        have hy3 : (state_y3 h hh x).val = 0 := by
          unfold state_y3
          exact h_succ2c_val_max _ hb_odd
        have hy2star : (y2star h hh x).val = h - 5 := by
          unfold y2star y2SwitchRow
          have h_nor : ¬(x.val = h + 1 ∨ x.val = h + 2 ∨ x.val = h + 3) := by omega
          rw [if_neg h_nor]
          change 2 * h - 1 - x.val = h - 5
          omega
        have hA2 : (A2 h hh x).val = h - 4 := by
          unfold A2
          rw [h_succ2c_val]
          · omega
          · omega
        have hjump : (jump_y h hh x).val = h - 3 := by
          unfold jump_y
          rw [h_succ2c_val]
          · omega
          · omega
        omega

  unfold row_map
  rw [if_neg h_not_jump]
  have h_cond : activeB2 h x (pred2c h hh (state_y3 h hh x)) := by
    rw [h_pred_y3]
    exact h_active
  rw [if_pos h_cond]
  rw [h_pred_y3]
  rfl

theorem pred2c_twice_val_of_ge_two (y : Fin (2 * h)) (hy : 2 ≤ y.val) :
  (pred2c h hh (pred2c h hh y)).val + 2 = y.val :=
by
  have pred_val : ∀ (x : Fin (2 * h)), x.val ≥ 1 → (pred2c h hh x).val = x.val - 1 := by
    intro x hx
    have h_le : one2 h hh ≤ x := by
      unfold one2
      exact hx
    have h_ite := Fin.coe_int_sub_eq_ite x (one2 h hh)
    rw [if_pos h_le] at h_ite
    unfold pred2c
    unfold one2 at h_ite ⊢
    push_cast at h_ite
    omega

  have hy1 : y.val ≥ 1 := by omega
  have eq1 : (pred2c h hh y).val = y.val - 1 := pred_val y hy1

  have hy2 : (pred2c h hh y).val ≥ 1 := by omega
  have eq2 : (pred2c h hh (pred2c h hh y)).val = (pred2c h hh y).val - 1 := pred_val (pred2c h hh y) hy2

  omega

theorem track2_seq_val_and_bound (x : Fin (2 * h)) (h_act : ∃ y, activeB2 h x y) (i : ℕ) (hi : i ≤ k_track2 h hh x) :
  (track2_seq h hh x i).val + 1 + 2 * i = (b_act h hh x).val ∧
  (i < k_track2 h hh x → (track2_seq h hh x i).val ≥ 2) :=
by
  obtain ⟨h_b_eq, h_L_eq, h_b_ge, h_L_ge⟩ := a_b_L_act_props h hh x h_act
  induction i with
  | zero =>
    have h_b_val_ge : 1 ≤ (b_act h hh x).val := by omega
    have H_raw := pred2c_val_of_ge_one h hh (b_act h hh x) h_b_val_ge
    change (track2_seq h hh x 0).val + 1 = (b_act h hh x).val at H_raw
    have H_eq : (track2_seq h hh x 0).val + 1 + 2 * 0 = (b_act h hh x).val := by omega
    constructor
    · exact H_eq
    · intro hi_lt
      have ha_ge : 0 ≤ (a_act h hh x).val := by omega
      omega
  | succ i ih =>
    have hi_lt : i < k_track2 h hh x := by omega
    have hi_le : i ≤ k_track2 h hh x := by omega
    obtain ⟨ih_eq, ih_bound⟩ := ih hi_le
    have h_val_ge_two : (track2_seq h hh x i).val ≥ 2 := ih_bound hi_lt
    have H_raw := pred2c_twice_val_of_ge_two h hh (track2_seq h hh x i) h_val_ge_two
    change (track2_seq h hh x (i + 1)).val + 2 = (track2_seq h hh x i).val at H_raw
    have H_eq : (track2_seq h hh x (i + 1)).val + 1 + 2 * (i + 1) = (b_act h hh x).val := by omega
    constructor
    · exact H_eq
    · intro hi_succ_lt
      have ha_ge : 0 ≤ (a_act h hh x).val := by omega
      omega

theorem jump_y_eq_a_act (x : Fin (2 * h)) (h_act : ∃ y, activeB2 h x y) :
  jump_y h hh x = a_act h hh x :=
by
  obtain ⟨y, hy⟩ := h_act
  unfold activeB2 at hy
  split_ifs at hy with heven
  · rcases hy with ⟨hx, _⟩ | ⟨hx, _⟩
    · apply Fin.ext
      have hx_eq : x.val = h + 1 ↔ True := iff_true_intro hx
      have h_switch : y2SwitchRow h x ↔ True := iff_true_intro (by
        unfold y2SwitchRow
        left
        exact hx)
      have h_even : h % 2 = 0 ↔ True := iff_true_intro heven
      unfold jump_y a_act A2 y2star succ2c one2 mMinusTwo2 mMinusOne2
      simp only [hx_eq, h_switch, h_even]
      change (((2 * h - 2 + 1) % (2 * h) + 1) % (2 * h) = 0)
      have h_mod1 : (2 * h - 2 + 1) % (2 * h) = 2 * h - 1 := by
        have : 2 * h - 2 + 1 = 2 * h - 1 := by omega
        rw [this]
        apply Nat.mod_eq_of_lt
        omega
      rw [h_mod1]
      have h_mod2 : (2 * h - 1 + 1) % (2 * h) = 0 := by
        have : 2 * h - 1 + 1 = 2 * h := by omega
        rw [this, Nat.mod_self]
      exact h_mod2

    · apply Fin.ext
      have hx_eq : x.val = h + 1 ↔ False := iff_false_intro (by intro h_contra; omega)
      have h_switch : y2SwitchRow h x ↔ False := iff_false_intro (by
        unfold y2SwitchRow
        rintro (h1 | h2 | h3) <;> omega)
      have h_even : h % 2 = 0 ↔ True := iff_true_intro heven
      unfold jump_y a_act A2 y2star succ2c one2 mMinusTwo2 mMinusOne2
      simp only [hx_eq, h_switch, h_even]
      change (((2 * h - 1 - x.val + 1) % (2 * h) + 1) % (2 * h) = h - 3)
      rw [hx]
      have h_mod1 : (2 * h - 1 - (h + 4) + 1) % (2 * h) = h - 4 := by
        have : 2 * h - 1 - (h + 4) + 1 = h - 4 := by omega
        rw [this]
        apply Nat.mod_eq_of_lt
        omega
      rw [h_mod1]
      have h_mod2 : (h - 4 + 1) % (2 * h) = h - 3 := by
        have : h - 4 + 1 = h - 3 := by omega
        rw [this]
        apply Nat.mod_eq_of_lt
        omega
      exact h_mod2

  · rcases hy with ⟨hx, _⟩ | ⟨hx, _⟩
    · apply Fin.ext
      have hx_eq : x.val = h + 1 ↔ True := iff_true_intro hx
      have h_switch : y2SwitchRow h x ↔ True := iff_true_intro (by
        unfold y2SwitchRow
        left
        exact hx)
      have h_even : h % 2 = 0 ↔ False := iff_false_intro heven
      unfold jump_y a_act A2 y2star succ2c one2 mMinusTwo2 mMinusOne2
      simp only [hx_eq, h_switch, h_even]
      change (((2 * h - 1 + 1) % (2 * h) + 1) % (2 * h) = 1)
      have h_mod1 : (2 * h - 1 + 1) % (2 * h) = 0 := by
        have : 2 * h - 1 + 1 = 2 * h := by omega
        rw [this, Nat.mod_self]
      rw [h_mod1]
      have h_mod2 : (0 + 1) % (2 * h) = 1 := by
        have : 0 + 1 = 1 := by omega
        rw [this]
        apply Nat.mod_eq_of_lt
        omega
      exact h_mod2

    · apply Fin.ext
      have hx_eq : x.val = h + 1 ↔ False := iff_false_intro (by intro h_contra; omega)
      have h_switch : y2SwitchRow h x ↔ False := iff_false_intro (by
        unfold y2SwitchRow
        rintro (h1 | h2 | h3) <;> omega)
      have h_even : h % 2 = 0 ↔ False := iff_false_intro heven
      unfold jump_y a_act A2 y2star succ2c one2 mMinusTwo2 mMinusOne2
      simp only [hx_eq, h_switch, h_even]
      change (((2 * h - 1 - x.val + 1) % (2 * h) + 1) % (2 * h) = h - 3)
      rw [hx]
      have h_mod1 : (2 * h - 1 - (h + 4) + 1) % (2 * h) = h - 4 := by
        have : 2 * h - 1 - (h + 4) + 1 = h - 4 := by omega
        rw [this]
        apply Nat.mod_eq_of_lt
        omega
      rw [h_mod1]
      have h_mod2 : (h - 4 + 1) % (2 * h) = h - 3 := by
        have : h - 4 + 1 = h - 3 := by omega
        rw [this]
        apply Nat.mod_eq_of_lt
        omega
      exact h_mod2

theorem track2_seq_end (x : Fin (2 * h)) (h_act : ∃ y, activeB2 h x y) :
  track2_seq h hh x (k_track2 h hh x) = jump_y h hh x :=
by
  have h1 := track2_seq_val_and_bound h hh x h_act (k_track2 h hh x) (by omega)
  have h2 := a_b_L_act_props h hh x h_act
  have h3 := jump_y_eq_a_act h hh x h_act
  have h1_val := h1.1
  have h2_1 := h2.1
  have h2_2 := h2.2.1
  rw [h3]
  apply Fin.ext
  omega

theorem track2_step_neq_jump (x : Fin (2 * h)) (h_act : ∃ y, activeB2 h x y) (i : ℕ) (hi : i < k_track2 h hh x) :
  track2_seq h hh x i ≠ jump_y h hh x :=
by
  intro heq
  have ⟨h1a, h1b, _, _⟩ := a_b_L_act_props h hh x h_act
  have ⟨h2a, _⟩ := track2_seq_val_and_bound h hh x h_act i (by omega)
  have h3 := jump_y_eq_a_act h hh x h_act
  have heq_val : (track2_seq h hh x i).val = (jump_y h hh x).val := congrArg Fin.val heq
  have h3_val : (jump_y h hh x).val = (a_act h hh x).val := congrArg Fin.val h3
  omega

theorem track2_pred_val_add_eq (x : Fin (2 * h)) (h_act : ∃ y, activeB2 h x y) (i : ℕ) (hi : i < k_track2 h hh x) :
  (pred2c h hh (track2_seq h hh x i)).val + 2 + 2 * i = (b_act h hh x).val :=
by
  have hi_le : i ≤ k_track2 h hh x := by omega
  have h1 := track2_seq_val_and_bound h hh x h_act i hi_le
  have h_eq : (track2_seq h hh x i).val + 1 + 2 * i = (b_act h hh x).val := h1.1
  have h_ge2 : (track2_seq h hh x i).val ≥ 2 := h1.2 hi
  have h_ge1 : 1 ≤ (track2_seq h hh x i).val := by omega
  have h_pred := pred2c_val_of_ge_one h hh (track2_seq h hh x i) h_ge1
  omega

theorem track2_step_active (x : Fin (2 * h)) (h_act : ∃ y, activeB2 h x y) (i : ℕ) (hi : i < k_track2 h hh x) :
  activeB2 h x (pred2c h hh (track2_seq h hh x i)) :=
by
  have H := activeB2_iff_in_interval h hh x (pred2c h hh (track2_seq h hh x i)) h_act
  rw [H]
  have ⟨h1a, h1b, h1c, h1d⟩ := a_b_L_act_props h hh x h_act
  have h2 := track2_pred_val_add_eq h hh x h_act i hi
  omega

theorem track2_seq_step (x : Fin (2 * h)) (h_act : ∃ y, activeB2 h x y) (i : ℕ) (hi : i < k_track2 h hh x) :
  row_map h hh x (track2_seq h hh x i) = track2_seq h hh x (i + 1) :=
by
  unfold row_map
  have h_neq := track2_step_neq_jump h hh x h_act i hi
  have h_active := track2_step_active h hh x h_act i hi
  rw [if_neg h_neq]
  rw [if_pos h_active]
  rfl

theorem track2_seq_iter (x : Fin (2 * h)) (h_act : ∃ y, activeB2 h x y) (k : ℕ) (hk : k ≤ k_track2 h hh x) :
  (row_map h hh x)^[k] (state_y4 h hh x) = track2_seq h hh x k :=
by
  induction k with
  | zero => rfl
  | succ n ih =>
    have hk_le : n ≤ k_track2 h hh x := by omega
    have hk_lt : n < k_track2 h hh x := by omega
    rw [iterate_succ_out]
    rw [ih hk_le]
    exact track2_seq_step h hh x h_act n hk_lt

theorem phase5_track2 (x : Fin (2 * h)) (h_act : ∃ y, activeB2 h x y) :
  (row_map h hh x)^[k_track2 h hh x] (state_y4 h hh x) = jump_y h hh x :=
by
  rw [track2_seq_iter h hh x h_act (k_track2 h hh x) (le_refl _)]
  exact track2_seq_end h hh x h_act

theorem active_phases_sum (x : Fin (2 * h)) :
  k_track2 h hh x + (k_trans_in h hh x + (k_out h hh x + (k_trans_out h hh x + k_track1 h hh x))) = 2 * h - 1 :=
by
  simp only [k_track2, k_trans_in, k_out, k_trans_out, k_track1, L_act]
  split_ifs <;> omega

theorem row_map_active_jump (x : Fin (2 * h)) (h_act : ∃ y, activeB2 h x y) :
  (row_map h hh x)^[2 * h - 1] (H_val h hh x) = jump_y h hh x :=
by
  rw [← active_phases_sum h hh x]
  rw [Function.iterate_add_apply, Function.iterate_add_apply, Function.iterate_add_apply, Function.iterate_add_apply]
  rw [phase1_track1 h hh x h_act]
  rw [phase2_trans_out h hh x h_act]
  rw [phase3_out h hh x h_act]
  rw [phase4_trans_in h hh x h_act]
  rw [phase5_track2 h hh x h_act]

theorem row_map_iter_jump (x : Fin (2 * h)) :
  (row_map h hh x)^[2 * h - 1] (H_val h hh x) = jump_y h hh x :=
by
  by_cases h_act : ∃ y, activeB2 h x y
  · exact row_map_active_jump h hh x h_act
  · have h_gen : ∀ y, ¬ activeB2 h x y := by
      intro y hy
      exact h_act ⟨y, hy⟩
    exact row_map_generic_jump h hh x h_gen

theorem r2Map_iter_2h_minus_1 (x : Fin (2 * h)) :
  (r2Map h hh)^[2 * h - 1] (x, H_val h hh x) = (x, jump_y h hh x) :=
by
  have hk : 2 * h - 1 < 2 * h := by omega
  rw [r2Map_iter_row h hh x (2 * h - 1) hk]
  rw [row_map_iter_jump h hh x]

theorem r2Map_apply_jump (x : Fin (2 * h)) :
  r2Map h hh (x, jump_y h hh x) = (succ2c h hh x, H_val h hh (succ2c h hh x)) :=
by
  haveI : NeZero (2 * h) := ⟨by omega⟩
  have h_pred_succ : ∀ y : Fin (2 * h), pred2c h hh (succ2c h hh y) = y := by
    intro y
    dsimp [pred2c, succ2c]
    exact add_sub_cancel_right y (one2 h hh)
  have H1 : pred2c h hh (jump_y h hh x) = A2 h hh x := by
    unfold jump_y
    exact h_pred_succ (A2 h hh x)
  dsimp [r2Map]
  rw [H1]
  rw [if_pos rfl]
  ext
  · rfl
  · unfold H_val
    rw [h_pred_succ x]
    unfold T_val
    rfl

theorem r2Map_row_step (x : Fin (2 * h)) :
  (r2Map h hh)^[2 * h] (x, H_val h hh x) = (succ2c h hh x, H_val h hh (succ2c h hh x)) :=
by
  rw [r2Map_unroll_last h hh x]
  rw [r2Map_iter_2h_minus_1 h hh x]
  rw [r2Map_apply_jump h hh x]

theorem r2Map_c_mul_2h_steps (x : Fin (2 * h)) (c : ℕ) :
  (r2Map h hh)^[c * (2 * h)] (x, H_val h hh x) = ((succ2c h hh)^[c] x, H_val h hh ((succ2c h hh)^[c] x)) :=
by
  rw [Nat.mul_comm c (2 * h), Function.iterate_mul]
  induction c with
  | zero => rfl
  | succ c ih =>
    have h_succ1 : ((r2Map h hh)^[2 * h])^[c + 1] (x, H_val h hh x) = (r2Map h hh)^[2 * h] (((r2Map h hh)^[2 * h])^[c] (x, H_val h hh x)) := by
      exact congr_fun (Function.iterate_succ' ((r2Map h hh)^[2 * h]) c) (x, H_val h hh x)
    have h_succ2 : ((succ2c h hh)^[c + 1] x) = succ2c h hh ((succ2c h hh)^[c] x) := by
      exact congr_fun (Function.iterate_succ' (succ2c h hh) c) x
    rw [h_succ1, h_succ2]
    rw [ih]
    rw [r2Map_row_step]

theorem succ2c_iter_eq_add (x : Fin (2 * h)) (c : ℕ) :
  (succ2c h hh)^[c] x = x + natToFin h hh c :=
by
  revert x
  induction c with
  | zero =>
    intro x
    ext
    change x.val = (x.val + 0 % (2 * h)) % (2 * h)
    rw [Nat.zero_mod, add_zero, Nat.mod_eq_of_lt x.isLt]
  | succ c' ih =>
    intro x
    have step_lemma : one2 h hh + natToFin h hh c' = natToFin h hh (c' + 1) := by
      ext
      change (1 + c' % (2 * h)) % (2 * h) = (c' + 1) % (2 * h)
      have h1 : 1 % (2 * h) = 1 := by
        apply Nat.mod_eq_of_lt
        omega
      calc (1 + c' % (2 * h)) % (2 * h)
        _ = (1 % (2 * h) + c' % (2 * h)) % (2 * h) := by rw [h1]
        _ = (1 + c') % (2 * h) := (Nat.add_mod 1 c' (2 * h)).symm
        _ = (c' + 1) % (2 * h) := by rw [Nat.add_comm 1 c']
    calc (succ2c h hh)^[c' + 1] x
      _ = (succ2c h hh)^[c'] (succ2c h hh x) := rfl
      _ = succ2c h hh x + natToFin h hh c' := ih (succ2c h hh x)
      _ = x + one2 h hh + natToFin h hh c' := rfl
      _ = x + (one2 h hh + natToFin h hh c') := by rw [add_assoc]
      _ = x + natToFin h hh (c' + 1) := by rw [step_lemma]

theorem natToFin_2h : natToFin h hh (2 * h) = zero2 h hh :=
by
  ext
  exact Nat.mod_self (2 * h)

theorem r2Map_full_cycle_H (x : Fin (2 * h)) :
  (r2Map h hh)^[(2 * h) * (2 * h)] (x, H_val h hh x) = (x, H_val h hh x) :=
by
  rw [r2Map_c_mul_2h_steps h hh x (2 * h)]
  have h_succ : (succ2c h hh)^[2 * h] x = x := by
    rw [succ2c_iter_eq_add]
    rw [natToFin_2h]
    apply Fin.ext
    change (x.val + 0) % (2 * h) = x.val
    rw [Nat.add_zero]
    exact Nat.mod_eq_of_lt x.isLt
  rw [h_succ]

theorem k_lt_of_div_zero (k : ℕ) (hm : 0 < 2 * h) (hdiv : k / (2 * h) = 0) : k < 2 * h :=
by
  rw [Nat.div_eq_zero_iff] at hdiv
  omega

theorem mod_eq_of_lt_2h (k : ℕ) (hk : k < 2 * h) : k % (2 * h) = k :=
by
  exact Nat.mod_eq_of_lt hk

theorem r2Map_no_early_return_H_c_lt (k : ℕ) (hk_lt : k < (2 * h) * (2 * h)) :
  k / (2 * h) < 2 * h :=
by
  have hpos : 0 < 2 * h := by cases h <;> omega
  first
  | exact Nat.div_lt_of_lt_mul hk_lt
  | exact Nat.div_lt_of_lt_mul hpos hk_lt
  | exact (Nat.div_lt_iff_lt_mul hpos).mpr hk_lt
  | exact Nat.div_lt_iff_lt_mul.mpr hk_lt

theorem r2Map_no_early_return_H_c_zero (x : Fin (2 * h)) (c : ℕ) (hc_lt : c < 2 * h)
  (heq : (succ2c h hh)^[c] x = x) : c = 0 :=
by
  have hx := x.isLt
  have h1_gen : ∀ (k : ℕ), ((succ2c h hh)^[k] x).val = (x.val + k) % (2 * h) := by
    intro k
    induction k with
    | zero =>
      change x.val = (x.val + 0) % (2 * h)
      rw [add_zero]
      exact (Nat.mod_eq_of_lt hx).symm
    | succ k' ih =>
      rw [Function.iterate_succ_apply']
      change (((succ2c h hh)^[k'] x).val + 1) % (2 * h) = (x.val + (k' + 1)) % (2 * h)
      rw [ih]
      have H2 : 1 % (2 * h) = 1 := by
        apply Nat.mod_eq_of_lt
        omega
      have H3 : (x.val + k' + 1) % (2 * h) = ((x.val + k') % (2 * h) + 1 % (2 * h)) % (2 * h) := Nat.add_mod (x.val + k') 1 (2 * h)
      rw [H2] at H3
      have H4 : x.val + (k' + 1) = x.val + k' + 1 := by omega
      rw [H4]
      exact H3.symm
  have h1 := h1_gen c
  have h2 : ((succ2c h hh)^[c] x).val = x.val := congrArg Fin.val heq
  rw [h1] at h2
  have h_cases : x.val + c < 2 * h ∨ 2 * h ≤ x.val + c := by omega
  rcases h_cases with h_lt | h_ge
  · have h3 : (x.val + c) % (2 * h) = x.val + c := Nat.mod_eq_of_lt h_lt
    rw [h3] at h2
    omega
  · have h3 : x.val + c = 2 * h + (x.val + c - 2 * h) := by omega
    have h4 : (2 * h + (x.val + c - 2 * h)) % (2 * h) = (x.val + c - 2 * h) % (2 * h) := by
      have H_add := Nat.add_mod (2 * h) (x.val + c - 2 * h) (2 * h)
      have H_self := Nat.mod_self (2 * h)
      rw [H_self, zero_add, Nat.mod_mod] at H_add
      exact H_add
    have h5 : (x.val + c - 2 * h) % (2 * h) = x.val + c - 2 * h := by
      apply Nat.mod_eq_of_lt
      omega
    rw [h3] at h2
    rw [h4, h5] at h2
    omega

theorem r2Map_iter_decompose_full (x : Fin (2 * h)) (k : ℕ) :
  (r2Map h hh)^[k] (x, H_val h hh x) =
    let c := k / (2 * h)
    let r := k % (2 * h)
    let xc := (succ2c h hh)^[c] x
    (xc, (row_map h hh xc)^[r] (H_val h hh xc)) :=
by
  change (r2Map h hh)^[k] (x, H_val h hh x) =
    ((succ2c h hh)^[k / (2 * h)] x,
      (row_map h hh ((succ2c h hh)^[k / (2 * h)] x))^[k % (2 * h)]
        (H_val h hh ((succ2c h hh)^[k / (2 * h)] x)))
  have hk : k = k % (2 * h) + k / (2 * h) * (2 * h) := by
    have h1 := Nat.mod_add_div k (2 * h)
    have h2 : (2 * h) * (k / (2 * h)) = k / (2 * h) * (2 * h) := Nat.mul_comm _ _
    rw [h2] at h1
    exact h1.symm
  conv_lhs => rw [hk]
  rw [Function.iterate_add]
  change (r2Map h hh)^[k % (2 * h)] ((r2Map h hh)^[k / (2 * h) * (2 * h)] (x, H_val h hh x)) =
    ((succ2c h hh)^[k / (2 * h)] x,
      (row_map h hh ((succ2c h hh)^[k / (2 * h)] x))^[k % (2 * h)]
        (H_val h hh ((succ2c h hh)^[k / (2 * h)] x)))
  rw [r2Map_c_mul_2h_steps h hh x (k / (2 * h))]
  have h_mod : k % (2 * h) < 2 * h := by
    apply Nat.mod_lt
    omega
  rw [r2Map_iter_row h hh ((succ2c h hh)^[k / (2 * h)] x) (k % (2 * h)) h_mod]

theorem single_cycle_transfer_lem {α : Type} [Fintype α] [DecidableEq α] (f : α → α) (a : α) (N : ℕ)
  (hN : Fintype.card α = N)
  (h_eq : f^[N] a = a) (h_neq : ∀ k, 0 < k → k < N → f^[k] a ≠ a) :
  (∀ p, f^[N] p = p) ∧ (∀ p k, 0 < k → k < N → f^[k] p ≠ p) :=
by
  have iter_add : ∀ (x y : ℕ) (c : α), f^[x + y] c = f^[x] (f^[y] c) := by
    intro x y
    induction y with
    | zero =>
      intro c
      rfl
    | succ y' ih =>
      intro c
      have h_idx : x + (y' + 1) = x + y' + 1 := by omega
      calc
        f^[x + (y' + 1)] c = f^[x + y' + 1] c := by rw [h_idx]
        _ = f^[x + y'] (f c) := rfl
        _ = f^[x] (f^[y'] (f c)) := ih (f c)
        _ = f^[x] (f^[y' + 1] c) := rfl

  have g_inj : Function.Injective (fun i : Fin N => f^[i.val] a) := by
    intro i j hij
    have hij' : f^[i.val] a = f^[j.val] a := hij
    have hi_lt : i.val < N := i.isLt
    have hj_lt : j.val < N := j.isLt
    cases lt_trichotomy i.val j.val with
    | inl h =>
      have h1 : f^[N - j.val + i.val] a = a := by
        calc
          f^[N - j.val + i.val] a = f^[N - j.val] (f^[i.val] a) := iter_add (N - j.val) i.val a
          _ = f^[N - j.val] (f^[j.val] a) := by rw [hij']
          _ = f^[N - j.val + j.val] a := (iter_add (N - j.val) j.val a).symm
          _ = f^[N] a := by
            have h_eq_idx : N - j.val + j.val = N := by omega
            exact congrArg (fun x => f^[x] a) h_eq_idx
          _ = a := h_eq
      have h2 : 0 < N - j.val + i.val := by omega
      have h3 : N - j.val + i.val < N := by omega
      exact False.elim (h_neq (N - j.val + i.val) h2 h3 h1)
    | inr h =>
      cases h with
      | inl h => apply Fin.eq_of_val_eq; exact h
      | inr h =>
        have h1 : f^[N - i.val + j.val] a = a := by
          calc
            f^[N - i.val + j.val] a = f^[N - i.val] (f^[j.val] a) := iter_add (N - i.val) j.val a
            _ = f^[N - i.val] (f^[i.val] a) := by rw [← hij']
            _ = f^[N - i.val + i.val] a := (iter_add (N - i.val) i.val a).symm
            _ = f^[N] a := by
              have h_eq_idx : N - i.val + i.val = N := by omega
              exact congrArg (fun x => f^[x] a) h_eq_idx
            _ = a := h_eq
        have h2 : 0 < N - i.val + j.val := by omega
        have h3 : N - i.val + j.val < N := by omega
        exact False.elim (h_neq (N - i.val + j.val) h2 h3 h1)

  have H_eq : Finset.image (fun i : Fin N => f^[i.val] a) Finset.univ = Finset.univ := by
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    rw [Finset.card_image_of_injective Finset.univ g_inj]
    have h1 : Finset.card (Finset.univ : Finset (Fin N)) = N := by
      rw [Finset.card_univ]
      simp
    have h2 : Finset.card (Finset.univ : Finset α) = N := by rw [Finset.card_univ, hN]
    omega

  have get_m (p : α) : ∃ m < N, p = f^[m] a := by
    have hp : p ∈ (Finset.univ : Finset α) := Finset.mem_univ p
    have h_eq_set : Finset.image (fun i : Fin N => f^[i.val] a) Finset.univ = Finset.univ := H_eq
    rw [← h_eq_set] at hp
    rcases Finset.mem_image.mp hp with ⟨i, _, hi⟩
    use i.val
    constructor
    · exact i.isLt
    · exact hi.symm

  constructor
  · intro p
    rcases get_m p with ⟨m, hm_lt, hm_eq⟩
    calc
      f^[N] p = f^[N] (f^[m] a) := by rw [hm_eq]
      _ = f^[N + m] a := (iter_add N m a).symm
      _ = f^[m + N] a := by
        have h_comm : N + m = m + N := by omega
        exact congrArg (fun x => f^[x] a) h_comm
      _ = f^[m] (f^[N] a) := iter_add m N a
      _ = f^[m] a := by rw [h_eq]
      _ = p := hm_eq.symm
  · intro p k hk_pos hk_lt hk_eq
    rcases get_m p with ⟨m, hm_lt, hm_eq⟩
    have h_iter : f^[k] (f^[m] a) = f^[m] a := by
      calc
        f^[k] (f^[m] a) = f^[k] p := by rw [← hm_eq]
        _ = p := hk_eq
        _ = f^[m] a := hm_eq
    have h_km : f^[k + m] a = f^[m] a := by
      calc
        f^[k + m] a = f^[k] (f^[m] a) := iter_add k m a
        _ = f^[m] a := h_iter

    by_cases h_lt_cases : k + m < N
    · have eq_idx : (⟨k + m, h_lt_cases⟩ : Fin N) = (⟨m, hm_lt⟩ : Fin N) := by
        apply g_inj
        exact h_km
      have eq_val : k + m = m := congrArg Fin.val eq_idx
      omega
    · have h_ge_cases : N ≤ k + m := by omega
      have h_r_lt : k + m - N < N := by omega
      have h_km_a : f^[k + m] a = f^[k + m - N] a := by
        calc
          f^[k + m] a = f^[(k + m - N) + N] a := by
            have h_eq_idx : k + m = (k + m - N) + N := by omega
            exact congrArg (fun x => f^[x] a) h_eq_idx
          _ = f^[k + m - N] (f^[N] a) := iter_add (k + m - N) N a
          _ = f^[k + m - N] a := by rw [h_eq]
      have h_r_eq_m : f^[k + m - N] a = f^[m] a := Eq.trans h_km_a.symm h_km
      have eq_idx : (⟨k + m - N, h_r_lt⟩ : Fin N) = (⟨m, hm_lt⟩ : Fin N) := by
        apply g_inj
        exact h_r_eq_m
      have eq_val : k + m - N = m := congrArg Fin.val eq_idx
      omega

theorem row_map_jump_eq_H_val (x : Fin (2 * h)) :
  row_map h hh x (jump_y h hh x) = H_val h hh x :=
by
  unfold row_map
  rw [if_pos rfl]

theorem row_map_iter_2h_H_val (x : Fin (2 * h)) :
  (row_map h hh x)^[2 * h] (H_val h hh x) = H_val h hh x :=
by
  have h_eq : 2 * h = 2 * h - 1 + 1 := by omega
  have step1 : (row_map h hh x)^[2 * h] (H_val h hh x) = (row_map h hh x)^[2 * h - 1 + 1] (H_val h hh x) :=
    congrArg (fun n => (row_map h hh x)^[n] (H_val h hh x)) h_eq
  rw [step1]
  rw [iterate_succ_out]
  rw [row_map_iter_jump]
  rw [row_map_jump_eq_H_val]

theorem pred2c_pred2c_neq_H_val (x y : Fin (2 * h))
  (h1 : y ≠ jump_y h hh x)
  (h2 : activeB2 h x (pred2c h hh y)) :
  pred2c h hh (pred2c h hh y) ≠ H_val h hh x :=
by
  intro h_eq
  have h_eq_val : (pred2c h hh (pred2c h hh y)).val = (H_val h hh x).val := congrArg Fin.val h_eq

  have val_pred2c : ∀ z : Fin (2 * h), (pred2c h hh z).val = if z.val = 0 then 2 * h - 1 else z.val - 1 := by
    intro z
    apply Nat.cast_injective (R := ℤ)
    have H : ((pred2c h hh z).val : ℤ) = ↑↑(z - (⟨1, by omega⟩ : Fin (2 * h))) := rfl
    rw [H, Fin.intCast_val_sub_eq_sub_add_ite]
    by_cases hz : z.val = 0
    · rw [if_pos hz]
      have h_not : ¬ ((⟨1, by omega⟩ : Fin (2 * h)) ≤ z) := by
        change ¬ (1 ≤ z.val)
        omega
      rw [if_neg h_not]
      push_cast
      omega
    · rw [if_neg hz]
      have h_yes : (⟨1, by omega⟩ : Fin (2 * h)) ≤ z := by
        change 1 ≤ z.val
        omega
      rw [if_pos h_yes]
      push_cast
      omega

  have val_succ2c : ∀ z : Fin (2 * h), (succ2c h hh z).val = if z.val = 2 * h - 1 then 0 else z.val + 1 := by
    intro z
    have H_eq : (succ2c h hh z).val = (z.val + 1) % (2 * h) := rfl
    rw [H_eq]
    by_cases hz : z.val = 2 * h - 1
    · rw [if_pos hz]
      rw [hz]
      have H : 2 * h - 1 + 1 = 2 * h := by omega
      rw [H, Nat.mod_self]
    · rw [if_neg hz]
      apply Nat.mod_eq_of_lt
      omega

  have H_val_h_plus_1 : x.val = h + 1 → (H_val h hh x).val = h - 1 := by
    intro hx
    have hp_x : (pred2c h hh x).val = h := by
      have H := val_pred2c x
      rw [hx] at H
      have h_not : ¬(h + 1 = 0) := by omega
      rw [if_neg h_not] at H
      omega
    have hy2s : (y2star h hh (pred2c h hh x)).val = h - 1 := by
      unfold y2star
      have h_sw : ¬ y2SwitchRow h (pred2c h hh x) := by
        unfold y2SwitchRow
        omega
      rw [if_neg h_sw]
      have h_mk : (⟨2 * h - 1 - (pred2c h hh x).val, by omega⟩ : Fin (2 * h)).val = 2 * h - 1 - (pred2c h hh x).val := rfl
      rw [h_mk]
      omega
    have ha2 : (A2 h hh (pred2c h hh x)).val = h := by
      unfold A2
      have H := val_succ2c (y2star h hh (pred2c h hh x))
      rw [hy2s] at H
      have h_cond : ¬ (h - 1 = 2 * h - 1) := by omega
      rw [if_neg h_cond] at H
      omega
    have H_val_eq : (H_val h hh x).val = h - 1 := by
      unfold H_val T_val
      have h_cond : ¬ ( (pred2c h hh x).val = h + 1 ∨ (pred2c h hh x).val = h + 2 ) := by omega
      rw [if_neg h_cond]
      have H3 := val_pred2c (A2 h hh (pred2c h hh x))
      rw [ha2] at H3
      have h_cond2 : ¬ (h = 0) := by omega
      rw [if_neg h_cond2] at H3
      omega
    exact H_val_eq

  have H_val_h_plus_4_even : h % 2 = 0 → x.val = h + 4 → (H_val h hh x).val = 2 * h - 2 := by
    intro h_mod hx
    have hp_x : (pred2c h hh x).val = h + 3 := by
      have H := val_pred2c x
      rw [hx] at H
      have h_not : ¬(h + 4 = 0) := by omega
      rw [if_neg h_not] at H
      omega
    have hy2s : (y2star h hh (pred2c h hh x)).val = 2 * h - 2 := by
      unfold y2star
      have h_sw : y2SwitchRow h (pred2c h hh x) := by
        unfold y2SwitchRow
        omega
      rw [if_pos h_sw, if_pos h_mod]
      rfl
    have ha2 : (A2 h hh (pred2c h hh x)).val = 2 * h - 1 := by
      unfold A2
      have H := val_succ2c (y2star h hh (pred2c h hh x))
      rw [hy2s] at H
      have h_cond : ¬ (2 * h - 2 = 2 * h - 1) := by omega
      rw [if_neg h_cond] at H
      omega
    have H_val_eq : (H_val h hh x).val = 2 * h - 2 := by
      unfold H_val T_val
      have h_cond : ¬ ( (pred2c h hh x).val = h + 1 ∨ (pred2c h hh x).val = h + 2 ) := by omega
      rw [if_neg h_cond]
      have H3 := val_pred2c (A2 h hh (pred2c h hh x))
      rw [ha2] at H3
      have h_cond2 : ¬ (2 * h - 1 = 0) := by omega
      rw [if_neg h_cond2] at H3
      omega
    exact H_val_eq

  have H_val_h_plus_4_odd : h % 2 ≠ 0 → x.val = h + 4 → (H_val h hh x).val = 2 * h - 1 := by
    intro h_mod hx
    have hp_x : (pred2c h hh x).val = h + 3 := by
      have H := val_pred2c x
      rw [hx] at H
      have h_not : ¬(h + 4 = 0) := by omega
      rw [if_neg h_not] at H
      omega
    have hy2s : (y2star h hh (pred2c h hh x)).val = 2 * h - 1 := by
      unfold y2star
      have h_sw : y2SwitchRow h (pred2c h hh x) := by
        unfold y2SwitchRow
        omega
      rw [if_pos h_sw, if_neg h_mod]
      rfl
    have ha2 : (A2 h hh (pred2c h hh x)).val = 0 := by
      unfold A2
      have H := val_succ2c (y2star h hh (pred2c h hh x))
      rw [hy2s] at H
      have h_cond : 2 * h - 1 = 2 * h - 1 := by rfl
      rw [if_pos h_cond] at H
      omega
    have H_val_eq : (H_val h hh x).val = 2 * h - 1 := by
      unfold H_val T_val
      have h_cond : ¬ ( (pred2c h hh x).val = h + 1 ∨ (pred2c h hh x).val = h + 2 ) := by omega
      rw [if_neg h_cond]
      have H3 := val_pred2c (A2 h hh (pred2c h hh x))
      rw [ha2] at H3
      have h_cond2 : 0 = 0 := by rfl
      rw [if_pos h_cond2] at H3
      omega
    exact H_val_eq

  dsimp [activeB2] at h2
  have hp1 := val_pred2c y
  have hp2 := val_pred2c (pred2c h hh y)

  by_cases h_mod : h % 2 = 0
  · rw [if_pos h_mod] at h2
    rcases h2 with ⟨hx, hy⟩ | ⟨hx, hy1, hy2⟩
    · have h_H := H_val_h_plus_1 hx
      rw [h_H] at h_eq_val
      by_cases hy0 : y.val = 0
      · rw [if_pos hy0] at hp1
        by_cases h_pred0 : (pred2c h hh y).val = 0
        · rw [if_pos h_pred0] at hp2; omega
        · rw [if_neg h_pred0] at hp2; omega
      · rw [if_neg hy0] at hp1
        by_cases h_pred0 : (pred2c h hh y).val = 0
        · rw [if_pos h_pred0] at hp2; omega
        · rw [if_neg h_pred0] at hp2; omega
    · have h_H := H_val_h_plus_4_even h_mod hx
      rw [h_H] at h_eq_val
      by_cases hy0 : y.val = 0
      · rw [if_pos hy0] at hp1
        by_cases h_pred0 : (pred2c h hh y).val = 0
        · rw [if_pos h_pred0] at hp2; omega
        · rw [if_neg h_pred0] at hp2; omega
      · rw [if_neg hy0] at hp1
        by_cases h_pred0 : (pred2c h hh y).val = 0
        · rw [if_pos h_pred0] at hp2; omega
        · rw [if_neg h_pred0] at hp2; omega
  · rw [if_neg h_mod] at h2
    rcases h2 with ⟨hx, hy1, hy2⟩ | ⟨hx, hy1⟩
    · have h_H := H_val_h_plus_1 hx
      rw [h_H] at h_eq_val
      by_cases hy0 : y.val = 0
      · rw [if_pos hy0] at hp1
        by_cases h_pred0 : (pred2c h hh y).val = 0
        · rw [if_pos h_pred0] at hp2; omega
        · rw [if_neg h_pred0] at hp2; omega
      · rw [if_neg hy0] at hp1
        by_cases h_pred0 : (pred2c h hh y).val = 0
        · rw [if_pos h_pred0] at hp2; omega
        · rw [if_neg h_pred0] at hp2; omega
    · have h_H := H_val_h_plus_4_odd h_mod hx
      rw [h_H] at h_eq_val
      by_cases hy0 : y.val = 0
      · rw [if_pos hy0] at hp1
        by_cases h_pred0 : (pred2c h hh y).val = 0
        · rw [if_pos h_pred0] at hp2; omega
        · rw [if_neg h_pred0] at hp2; omega
      · rw [if_neg hy0] at hp1
        by_cases h_pred0 : (pred2c h hh y).val = 0
        · rw [if_pos h_pred0] at hp2; omega
        · rw [if_neg h_pred0] at hp2; omega

theorem H_val_eq_pred_jump (x : Fin (2 * h)) (h_gen : ∀ y, ¬ activeB2 h x y) :
  H_val h hh x = pred2c h hh (jump_y h hh x) :=
by
  haveI : NeZero (2 * h) := ⟨by omega⟩

  have h_succ2c_val_of_lt {z : Fin (2 * h)} (hz : z.val + 1 < 2 * h) : (succ2c h hh z).val = z.val + 1 := by
    unfold succ2c one2
    rw [Fin.val_add_eq_ite]
    have h_one : (⟨1, by omega⟩ : Fin (2 * h)).val = 1 := rfl
    rw [h_one]
    split_ifs with h_cond
    · omega
    · rfl

  have h_succ2c_val_of_eq {z : Fin (2 * h)} (hz : z.val + 1 = 2 * h) : (succ2c h hh z).val = 0 := by
    unfold succ2c one2
    rw [Fin.val_add_eq_ite]
    have h_one : (⟨1, by omega⟩ : Fin (2 * h)).val = 1 := rfl
    rw [h_one]
    split_ifs with h_cond
    · omega
    · omega

  have pred2c_succ2c (y : Fin (2 * h)) : pred2c h hh (succ2c h hh y) = y := by
    unfold pred2c succ2c
    exact add_sub_cancel_right y (one2 h hh)

  have succ2c_pred2c (y : Fin (2 * h)) : succ2c h hh (pred2c h hh y) = y := by
    unfold pred2c succ2c
    exact sub_add_cancel y (one2 h hh)

  have pred_eq_of_succ_eq (y z : Fin (2 * h)) (h_eq : y = succ2c h hh z) : pred2c h hh y = z := by
    rw [h_eq, pred2c_succ2c]

  have hx1 : x.val ≠ h + 1 := by
    intro hx
    by_cases h_mod : h % 2 = 0
    · have hy : activeB2 h x ⟨0, by omega⟩ := by
        unfold activeB2
        rw [if_pos h_mod]
        left
        constructor
        · exact hx
        · change 0 ≤ h - 1
          omega
      exact h_gen _ hy
    · have hy : activeB2 h x ⟨1, by omega⟩ := by
        unfold activeB2
        rw [if_neg h_mod]
        left
        constructor
        · exact hx
        · constructor
          · change 1 ≤ 1
            omega
          · change 1 ≤ h - 1
            omega
      exact h_gen _ hy

  have hx4 : x.val ≠ h + 4 := by
    intro hx
    by_cases h_mod : h % 2 = 0
    · have hy : activeB2 h x ⟨h - 3, by omega⟩ := by
        unfold activeB2
        rw [if_pos h_mod]
        right
        constructor
        · exact hx
        · constructor
          · change h - 3 ≤ h - 3
            omega
          · change h - 3 ≤ 2 * h - 2
            omega
      exact h_gen _ hy
    · have hy : activeB2 h x ⟨h - 3, by omega⟩ := by
        unfold activeB2
        rw [if_neg h_mod]
        right
        constructor
        · exact hx
        · change h - 3 ≤ h - 3
          omega
      exact h_gen _ hy

  unfold H_val T_val jump_y
  rw [pred2c_succ2c]

  by_cases hx2 : x.val = h + 2
  · have h_pred : pred2c h hh x = ⟨h + 1, by omega⟩ := by
      apply pred_eq_of_succ_eq
      apply Fin.ext
      have hz : (⟨h + 1, by omega⟩ : Fin (2 * h)).val + 1 < 2 * h := by
        change h + 1 + 1 < 2 * h
        omega
      rw [h_succ2c_val_of_lt hz]
      have h_val : (⟨h + 1, by omega⟩ : Fin (2 * h)).val = h + 1 := rfl
      rw [h_val]
      omega
    have h_pred_val : (pred2c h hh x).val = h + 1 := congrArg Fin.val h_pred
    have h_cond : (pred2c h hh x).val = h + 1 ∨ (pred2c h hh x).val = h + 2 := Or.inl h_pred_val
    simp only [h_cond, if_true]

    unfold A2 y2star y2SwitchRow
    have hx_sw : x.val = h + 1 ∨ x.val = h + 2 ∨ x.val = h + 3 := Or.inr (Or.inl hx2)
    have hpred_sw : (pred2c h hh x).val = h + 1 ∨ (pred2c h hh x).val = h + 2 ∨ (pred2c h hh x).val = h + 3 := Or.inl h_pred_val
    simp only [hx_sw, hpred_sw, if_true]

  · by_cases hx3 : x.val = h + 3
    · have h_pred : pred2c h hh x = ⟨h + 2, by omega⟩ := by
        apply pred_eq_of_succ_eq
        apply Fin.ext
        have hz : (⟨h + 2, by omega⟩ : Fin (2 * h)).val + 1 < 2 * h := by
          change h + 2 + 1 < 2 * h
          omega
        rw [h_succ2c_val_of_lt hz]
        have h_val : (⟨h + 2, by omega⟩ : Fin (2 * h)).val = h + 2 := rfl
        rw [h_val]
        omega
      have h_pred_val : (pred2c h hh x).val = h + 2 := congrArg Fin.val h_pred
      have h_cond : (pred2c h hh x).val = h + 1 ∨ (pred2c h hh x).val = h + 2 := Or.inr h_pred_val
      simp only [h_cond, if_true]

      unfold A2 y2star y2SwitchRow
      have hx_sw : x.val = h + 1 ∨ x.val = h + 2 ∨ x.val = h + 3 := Or.inr (Or.inr hx3)
      have hpred_sw : (pred2c h hh x).val = h + 1 ∨ (pred2c h hh x).val = h + 2 ∨ (pred2c h hh x).val = h + 3 := Or.inr (Or.inl h_pred_val)
      simp only [hx_sw, hpred_sw, if_true]

    · have h_pred_val_not1 : (pred2c h hh x).val ≠ h + 1 := by
        intro h_eq
        have h_this : pred2c h hh x = ⟨h + 1, by omega⟩ := Fin.ext h_eq
        have h_x_eq : succ2c h hh (pred2c h hh x) = succ2c h hh ⟨h + 1, by omega⟩ := congrArg (succ2c h hh) h_this
        rw [succ2c_pred2c] at h_x_eq
        have h_x_val : x.val = h + 2 := by
          have h_x_val' := congrArg Fin.val h_x_eq
          have hz : (⟨h + 1, by omega⟩ : Fin (2 * h)).val + 1 < 2 * h := by
            change h + 1 + 1 < 2 * h
            omega
          rw [h_succ2c_val_of_lt hz] at h_x_val'
          have h_val : (⟨h + 1, by omega⟩ : Fin (2 * h)).val = h + 1 := rfl
          rw [h_val] at h_x_val'
          omega
        exact hx2 h_x_val

      have h_pred_val_not2 : (pred2c h hh x).val ≠ h + 2 := by
        intro h_eq
        have h_this : pred2c h hh x = ⟨h + 2, by omega⟩ := Fin.ext h_eq
        have h_x_eq : succ2c h hh (pred2c h hh x) = succ2c h hh ⟨h + 2, by omega⟩ := congrArg (succ2c h hh) h_this
        rw [succ2c_pred2c] at h_x_eq
        have h_x_val : x.val = h + 3 := by
          have h_x_val' := congrArg Fin.val h_x_eq
          have hz : (⟨h + 2, by omega⟩ : Fin (2 * h)).val + 1 < 2 * h := by
            change h + 2 + 1 < 2 * h
            omega
          rw [h_succ2c_val_of_lt hz] at h_x_val'
          have h_val : (⟨h + 2, by omega⟩ : Fin (2 * h)).val = h + 2 := rfl
          rw [h_val] at h_x_val'
          omega
        exact hx3 h_x_val

      have h_pred_val_not3 : (pred2c h hh x).val ≠ h + 3 := by
        intro h_eq
        have h_this : pred2c h hh x = ⟨h + 3, by omega⟩ := Fin.ext h_eq
        have h_x_eq : succ2c h hh (pred2c h hh x) = succ2c h hh ⟨h + 3, by omega⟩ := congrArg (succ2c h hh) h_this
        rw [succ2c_pred2c] at h_x_eq
        have h_x_val : x.val = h + 4 := by
          have h_x_val' := congrArg Fin.val h_x_eq
          have hz : (⟨h + 3, by omega⟩ : Fin (2 * h)).val + 1 < 2 * h := by
            change h + 3 + 1 < 2 * h
            omega
          rw [h_succ2c_val_of_lt hz] at h_x_val'
          have h_val : (⟨h + 3, by omega⟩ : Fin (2 * h)).val = h + 3 := rfl
          rw [h_val] at h_x_val'
          omega
        exact hx4 h_x_val

      have h_cond : ¬ ((pred2c h hh x).val = h + 1 ∨ (pred2c h hh x).val = h + 2) := by
        intro h_or
        cases h_or with
        | inl h1 => exact h_pred_val_not1 h1
        | inr h2 => exact h_pred_val_not2 h2
      simp only [h_cond, if_false]

      have hx_sw_false : ¬ y2SwitchRow h x := by
        unfold y2SwitchRow
        intro h_or
        cases h_or with
        | inl h1 => exact hx1 h1
        | inr h23 =>
          cases h23 with
          | inl h2 => exact hx2 h2
          | inr h3 => exact hx3 h3

      have hpred_sw_false : ¬ y2SwitchRow h (pred2c h hh x) := by
        unfold y2SwitchRow
        intro h_or
        cases h_or with
        | inl h1 => exact h_pred_val_not1 h1
        | inr h23 =>
          cases h23 with
          | inl h2 => exact h_pred_val_not2 h2
          | inr h3 => exact h_pred_val_not3 h3

      unfold A2 y2star
      simp only [hx_sw_false, hpred_sw_false, if_false]

      rw [pred2c_succ2c]
      apply Fin.ext

      have h_lhs_val : ∀ P, ↑(⟨2 * h - 1 - ↑(pred2c h hh x), P⟩ : Fin (2 * h)) = 2 * h - 1 - ↑(pred2c h hh x) := fun _ => rfl

      have h_rhs_val_0 : ∀ P, x.val = 0 → ↑(succ2c h hh ⟨2 * h - 1 - ↑x, P⟩) = 0 := by
        intro P h_x
        apply h_succ2c_val_of_eq
        change 2 * h - 1 - x.val + 1 = 2 * h
        omega

      have h_rhs_val_not0 : ∀ P, x.val ≠ 0 → ↑(succ2c h hh ⟨2 * h - 1 - ↑x, P⟩) = 2 * h - 1 - ↑x + 1 := by
        intro P h_x
        apply h_succ2c_val_of_lt
        change 2 * h - 1 - x.val + 1 < 2 * h
        omega

      by_cases hx0 : x.val = 0
      · have h_pred_x_0 : pred2c h hh x = ⟨2 * h - 1, by omega⟩ := by
          apply pred_eq_of_succ_eq
          apply Fin.ext
          have hz : (⟨2 * h - 1, by omega⟩ : Fin (2 * h)).val + 1 = 2 * h := by
            change 2 * h - 1 + 1 = 2 * h
            omega
          rw [h_succ2c_val_of_eq hz]
          exact hx0
        have h_pred_val_0 : (pred2c h hh x).val = 2 * h - 1 := congrArg Fin.val h_pred_x_0

        rw [h_lhs_val, h_rhs_val_0 _ hx0]
        omega

      · have h_pred_x_not0 : pred2c h hh x = ⟨x.val - 1, by omega⟩ := by
          apply pred_eq_of_succ_eq
          apply Fin.ext
          have hz : (⟨x.val - 1, by omega⟩ : Fin (2 * h)).val + 1 < 2 * h := by
            change x.val - 1 + 1 < 2 * h
            omega
          rw [h_succ2c_val_of_lt hz]
          have h_val : (⟨x.val - 1, by omega⟩ : Fin (2 * h)).val = x.val - 1 := rfl
          rw [h_val]
          omega
        have h_pred_val_not0 : (pred2c h hh x).val = x.val - 1 := congrArg Fin.val h_pred_x_not0

        rw [h_lhs_val, h_rhs_val_not0 _ hx0]
        omega

theorem pred2c_inj (a b : Fin (2 * h))
  (heq : pred2c h hh a = pred2c h hh b) : a = b :=
by
  -- Provide the non-zero instance for 2 * h so that Fin (2 * h) is recognized as an AddCommGroup.
  haveI : NeZero (2 * h) := ⟨by omega⟩
  -- Unfold the definition of pred2c implicitly by changing to a definitional equality
  have eq1 : a - one2 h hh = b - one2 h hh := heq
  -- Use the group property that subtracting and then adding the same element cancels out
  calc
    a = a - one2 h hh + one2 h hh := (sub_add_cancel a (one2 h hh)).symm
    _ = b - one2 h hh + one2 h hh := by rw [eq1]
    _ = b := sub_add_cancel b (one2 h hh)

theorem b_act_is_active (x : Fin (2 * h))
  (h_act : ∃ z, activeB2 h x z) : activeB2 h x (b_act h hh x) :=
by
  have h_cases : x.val = h + 1 ∨ x.val = h + 4 := by
    rcases h_act with ⟨z, hz⟩
    unfold activeB2 at hz
    split_ifs at hz
    · rcases hz with ⟨h1, _⟩ | ⟨h4, _⟩
      · exact Or.inl h1
      · exact Or.inr h4
    · rcases hz with ⟨h1, _⟩ | ⟨h4, _⟩
      · exact Or.inl h1
      · exact Or.inr h4
  have hb : (b_act h hh x).val = if x.val = h + 1 then h - 1 else if h % 2 = 0 then 2 * h - 2 else 2 * h - 1 := by
    unfold b_act
    split_ifs <;> rfl
  unfold activeB2
  rw [hb]
  rcases h_cases with hx1 | hx4
  · split_ifs <;> (left; omega)
  · split_ifs <;> (right; omega)

theorem pred2c_neq_H_val (x y : Fin (2 * h))
  (h1 : y ≠ jump_y h hh x)
  (h2 : ¬activeB2 h x (pred2c h hh y)) :
  pred2c h hh y ≠ H_val h hh x :=
by
  intro h_eq
  by_cases h_act : ∃ z, activeB2 h x z
  · have h_H := H_val_eq_b_act h hh x h_act
    have h_b_act := b_act_is_active h hh x h_act
    rw [h_H] at h_eq
    rw [h_eq] at h2
    exact h2 h_b_act
  · push_neg at h_act
    have h_H := H_val_eq_pred_jump h hh x h_act
    have h_pred_y : pred2c h hh y = pred2c h hh (jump_y h hh x) := by
      rw [h_H] at h_eq
      exact h_eq
    have h_y_eq := pred2c_inj h hh y (jump_y h hh x) h_pred_y
    exact h1 h_y_eq

theorem row_map_eq_H_val_iff (x y : Fin (2 * h)) :
  row_map h hh x y = H_val h hh x ↔ y = jump_y h hh x :=
by
  constructor
  · intro h_eq
    by_cases h1 : y = jump_y h hh x
    · exact h1
    · unfold row_map at h_eq
      rw [if_neg h1] at h_eq
      by_cases h2 : activeB2 h x (pred2c h hh y)
      · rw [if_pos h2] at h_eq
        exfalso
        exact pred2c_pred2c_neq_H_val h hh x y h1 h2 h_eq
      · rw [if_neg h2] at h_eq
        exfalso
        exact pred2c_neq_H_val h hh x y h1 h2 h_eq
  · intro h_eq
    rw [h_eq]
    unfold row_map
    exact if_pos rfl

theorem row_map_iter_not_H_val (x : Fin (2 * h)) (k : ℕ) (hk0 : 0 < k) (hk_lt : k < 2 * h) :
  (row_map h hh x)^[k] (H_val h hh x) ≠ H_val h hh x :=
by
  intro h_eq
  cases k with
  | zero => omega
  | succ k_prev =>
    have hk_prev_lt : k_prev < 2 * h - 1 := by omega
    have h_iter : row_map h hh x ((row_map h hh x)^[k_prev] (H_val h hh x)) = H_val h hh x := by
      have h1 : (row_map h hh x)^[k_prev.succ] (H_val h hh x) = H_val h hh x := h_eq
      rw [Function.iterate_succ_apply'] at h1
      exact h1
    rw [row_map_eq_H_val_iff] at h_iter
    have h_not_jump := row_map_iter_not_jump h hh x k_prev hk_prev_lt
    exact h_not_jump h_iter

theorem row_map_single_cycle (x : Fin (2 * h)) :
  (∀ y : Fin (2 * h), (row_map h hh x)^[2 * h] y = y) ∧
  (∀ (y : Fin (2 * h)) (k : ℕ), 0 < k → k < 2 * h → (row_map h hh x)^[k] y ≠ y) :=
by
  exact single_cycle_transfer_lem (row_map h hh x) (H_val h hh x) (2 * h) (Fintype.card_fin (2 * h)) (row_map_iter_2h_H_val h hh x) (row_map_iter_not_H_val h hh x)

theorem r2Map_no_early_return_H (x : Fin (2 * h)) (k : ℕ)
  (hk0 : 0 < k) (hk_lt : k < (2 * h) * (2 * h)) :
  (r2Map h hh)^[k] (x, H_val h hh x) ≠ (x, H_val h hh x) :=
by
  intro heq
  have h_decomp := r2Map_iter_decompose_full h hh x k
  rw [heq] at h_decomp
  have h_eq_fst : (succ2c h hh)^[k / (2 * h)] x = x := congr_arg Prod.fst h_decomp.symm
  have h_eq_snd : (row_map h hh ((succ2c h hh)^[k / (2 * h)] x))^[k % (2 * h)] (H_val h hh ((succ2c h hh)^[k / (2 * h)] x)) = H_val h hh x := congr_arg Prod.snd h_decomp.symm
  have hm : 0 < 2 * h := by omega
  have hc_lt : k / (2 * h) < 2 * h := r2Map_no_early_return_H_c_lt h k hk_lt
  have hc_zero : k / (2 * h) = 0 := r2Map_no_early_return_H_c_zero h hh x (k / (2 * h)) hc_lt h_eq_fst
  have hk_lt_2h : k < 2 * h := k_lt_of_div_zero h k hm hc_zero
  have hr : k % (2 * h) = k := mod_eq_of_lt_2h h k hk_lt_2h
  rw [h_eq_fst] at h_eq_snd
  rw [hr] at h_eq_snd
  have h_cycle := (row_map_single_cycle h hh x).right (H_val h hh x) k hk0 hk_lt_2h
  exact h_cycle h_eq_snd

theorem single_cycle_transfer {α : Type} [Fintype α] [DecidableEq α] (f : α → α) (a : α) (N : ℕ)
  (hN : Fintype.card α = N)
  (h_eq : f^[N] a = a) (h_neq : ∀ k, 0 < k → k < N → f^[k] a ≠ a) :
  (∀ p, f^[N] p = p) ∧ (∀ p k, 0 < k → k < N → f^[k] p ≠ p) :=
by
  let g : Fin N → α := fun i => f^[i.val] a
  have inj_g : ∀ i j : Fin N, g i = g j → i = j := by
    intro i j hij
    have hij' : f^[i.val] a = f^[j.val] a := hij
    by_cases h1 : i.val < j.val
    · have h_eq1 : f^[(N - j.val) + i.val] a = a := by
        calc f^[(N - j.val) + i.val] a
          _ = (f^[N - j.val] ∘ f^[i.val]) a := by rw [Function.iterate_add]
          _ = f^[N - j.val] (f^[i.val] a) := rfl
          _ = f^[N - j.val] (f^[j.val] a) := by rw [hij']
          _ = (f^[N - j.val] ∘ f^[j.val]) a := rfl
          _ = f^[(N - j.val) + j.val] a := by rw [← Function.iterate_add]
          _ = f^[N] a := by
            have h_sum : N - j.val + j.val = N := by omega
            rw [h_sum]
          _ = a := h_eq
      have h2 : 0 < (N - j.val) + i.val := by omega
      have h3 : (N - j.val) + i.val < N := by omega
      exact False.elim (h_neq ((N - j.val) + i.val) h2 h3 h_eq1)
    · by_cases h2 : j.val < i.val
      · have h_eq1 : f^[(N - i.val) + j.val] a = a := by
          calc f^[(N - i.val) + j.val] a
            _ = (f^[N - i.val] ∘ f^[j.val]) a := by rw [Function.iterate_add]
            _ = f^[N - i.val] (f^[j.val] a) := rfl
            _ = f^[N - i.val] (f^[i.val] a) := by rw [←hij']
            _ = (f^[N - i.val] ∘ f^[i.val]) a := rfl
            _ = f^[(N - i.val) + i.val] a := by rw [← Function.iterate_add]
            _ = f^[N] a := by
              have h_sum : N - i.val + i.val = N := by omega
              rw [h_sum]
            _ = a := h_eq
        have h3 : 0 < (N - i.val) + j.val := by omega
        have h4 : (N - i.val) + j.val < N := by omega
        exact False.elim (h_neq ((N - i.val) + j.val) h3 h4 h_eq1)
      · have heq : i.val = j.val := by omega
        exact Fin.ext heq

  have h_image_card : (Finset.univ.image g).card = N := by
    have h_inj : Function.Injective g := fun i j hij => inj_g i j hij
    have h_card := Finset.card_image_of_injective Finset.univ h_inj
    rw [h_card, Finset.card_univ, Fintype.card_fin]

  have h_image_eq : Finset.univ.image g = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [h_image_card]
    exact hN.symm

  have h_surj : ∀ p : α, ∃ i : Fin N, g i = p := by
    intro p
    have hp : p ∈ Finset.univ.image g := by
      rw [h_image_eq]
      exact Finset.mem_univ p
    rcases Finset.mem_image.mp hp with ⟨i, _, hi⟩
    exact ⟨i, hi⟩

  have H_eq : ∀ p, f^[N] p = p := by
    intro p
    rcases h_surj p with ⟨i, hi⟩
    have hi' : f^[i.val] a = p := hi
    rw [← hi']
    calc f^[N] (f^[i.val] a)
      _ = (f^[N] ∘ f^[i.val]) a := rfl
      _ = f^[N + i.val] a := by rw [← Function.iterate_add]
      _ = f^[i.val + N] a := by
        have h_comm : N + i.val = i.val + N := by omega
        rw [h_comm]
      _ = (f^[i.val] ∘ f^[N]) a := by rw [Function.iterate_add]
      _ = f^[i.val] (f^[N] a) := rfl
      _ = f^[i.val] a := by rw [h_eq]

  constructor
  · exact H_eq
  · intros p k hk_pos hk_lt
    rcases h_surj p with ⟨i, hi⟩
    have hi' : f^[i.val] a = p := hi
    rw [← hi']
    intro h_contra
    have eq1 : f^[N - i.val] (f^[k] (f^[i.val] a)) = f^[N - i.val] (f^[i.val] a) := by rw [h_contra]
    have rhs_eq : f^[N - i.val] (f^[i.val] a) = a := by
      calc f^[N - i.val] (f^[i.val] a)
        _ = (f^[N - i.val] ∘ f^[i.val]) a := rfl
        _ = f^[(N - i.val) + i.val] a := by rw [← Function.iterate_add]
        _ = f^[N] a := by
          have h_sum : N - i.val + i.val = N := by omega
          rw [h_sum]
        _ = a := h_eq
    have lhs_eq : f^[N - i.val] (f^[k] (f^[i.val] a)) = f^[k] a := by
      calc f^[N - i.val] (f^[k] (f^[i.val] a))
        _ = (f^[N - i.val] ∘ f^[k]) (f^[i.val] a) := rfl
        _ = f^[(N - i.val) + k] (f^[i.val] a) := by rw [← Function.iterate_add]
        _ = (f^[(N - i.val) + k] ∘ f^[i.val]) a := rfl
        _ = f^[(N - i.val) + k + i.val] a := by rw [← Function.iterate_add]
        _ = f^[k + N] a := by
          have h_sum : (N - i.val) + k + i.val = k + N := by omega
          rw [h_sum]
        _ = (f^[k] ∘ f^[N]) a := by rw [Function.iterate_add]
        _ = f^[k] (f^[N] a) := rfl
        _ = f^[k] a := by rw [h_eq]
    rw [rhs_eq, lhs_eq] at eq1
    exact h_neq k hk_pos hk_lt eq1

theorem color2_singleCycle_unrolled (h6 : 6 ≤ h) : (∀ p : Fin (2 * h) × Fin (2 * h), (r2Map h hh)^[(2 * h) * (2 * h)] p = p) ∧
    (∀ (p : Fin (2 * h) × Fin (2 * h)) (k : ℕ), 0 < k → k < (2 * h) * (2 * h) → (r2Map h hh)^[k] p ≠ p) :=
by
  exact single_cycle_transfer (r2Map h hh) (zero2 h hh, H_val h hh (zero2 h hh)) ((2 * h) * (2 * h))
    (card_fiber2 h)
    (r2Map_full_cycle_H h hh (zero2 h hh))
    (r2Map_no_early_return_H h hh (zero2 h hh))
