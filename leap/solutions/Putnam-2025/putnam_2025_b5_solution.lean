import Mathlib
open Finset
open BigOperators
abbrev modInv (p : ℕ) (k : ℕ) : ℕ := ZMod.val ((k : ZMod p)⁻¹)
abbrev descentCount (p : ℕ) : ℕ :=
  #{k ∈ Finset.Icc 1 (p - 2) | modInv p (k + 1) < modInv p k}

def J_set (p : ℕ) : Finset ℕ := Finset.Icc 2 (p - 2)
def D_J (p : ℕ) : Finset ℕ :=
  Finset.filter (fun (u : ℕ) => (p : ℤ) + 3 ≤ (u : ℤ) + (modInv p u : ℤ)) (J_set p)
def B_J (p : ℕ) : Finset ℕ :=
  Finset.filter (fun (u : ℕ) => (u : ℤ) + (modInv p u : ℤ) ≤ (p : ℤ) - 3) (J_set p)
def C_J (p : ℕ) : Finset ℕ :=
  Finset.filter (fun (u : ℕ) => (p : ℤ) - 2 ≤ (u : ℤ) + (modInv p u : ℤ) ∧ (u : ℤ) + (modInv p u : ℤ) ≤ (p : ℤ) + 2) (J_set p)

def symm_map (p u : ℕ) : ℕ :=
  Int.toNat ((p : ℤ) - (u : ℤ))

theorem descent_count_5 : descentCount 5 = 1 :=
by
 rfl

theorem descent_count_7 : descentCount 7 = 1 :=
by
  rfl

theorem descentCount_eq (p : ℕ) (hp_prime : p.Prime) :
  descentCount p = (Finset.filter (fun y => modInv p (y + 1) < modInv p y) (Finset.Icc 1 (p - 2))).card :=
rfl

theorem zmod_cast_eq_zero_iff_dvd (p y : ℕ) : (y : ZMod p) = 0 ↔ p ∣ y :=
CharP.cast_eq_zero_iff (ZMod p) p y

theorem not_dvd_of_pos_of_lt (p y : ℕ) (hy1 : 1 ≤ y) (hyp : y < p) : ¬ p ∣ y :=
by
  intro h
  have hy0 : 0 < y := by omega
  have hle : p ≤ y := Nat.le_of_dvd hy0 h
  omega

theorem zmod_cast_ne_zero (p : ℕ) (y : ℕ) (hy1 : 1 ≤ y) (hyp : y < p) :
  (y : ZMod p) ≠ 0 :=
by
  intro h
  -- Transform the assumption that (y : ZMod p) = 0 into p ∣ y
  have h_dvd : p ∣ y := (zmod_cast_eq_zero_iff_dvd p y).mp h
  -- Apply our helper lemma to derive the contradiction
  exact not_dvd_of_pos_of_lt p y hy1 hyp h_dvd

theorem modInv_def_lemma (p y : ℕ) [Fact p.Prime] :
  modInv p y = ZMod.val ((y : ZMod p)⁻¹) :=
rfl

theorem zmod_val_eq_zero_iff {p : ℕ} [Fact p.Prime] (x : ZMod p) :
  ZMod.val x = 0 ↔ x = 0 :=
by
  exact ZMod.val_eq_zero x

theorem zmod_inv_eq_zero_iff {p : ℕ} [Fact p.Prime] (x : ZMod p) :
  x⁻¹ = 0 ↔ x = 0 :=
inv_eq_zero

theorem modInv_eq_zero_iff (p : ℕ) [Fact p.Prime] (y : ℕ) :
  modInv p y = 0 ↔ (y : ZMod p) = 0 :=
by
  have h1 : modInv p y = 0 ↔ ZMod.val ((y : ZMod p)⁻¹) = 0 := by
    rw [modInv_def_lemma p y]
  have h2 : ZMod.val ((y : ZMod p)⁻¹) = 0 ↔ (y : ZMod p)⁻¹ = 0 :=
    zmod_val_eq_zero_iff ((y : ZMod p)⁻¹)
  have h3 : (y : ZMod p)⁻¹ = 0 ↔ (y : ZMod p) = 0 :=
    zmod_inv_eq_zero_iff (y : ZMod p)
  exact Iff.trans h1 (Iff.trans h2 h3)

theorem modInv_ne_zero (p : ℕ) (hp_prime : p.Prime) (y : ℕ) (hy1 : 1 ≤ y) (hyp : y < p) :
  modInv p y ≠ 0 :=
by
  intro h
  have hFact : Fact p.Prime := ⟨hp_prime⟩
  -- Apply the equivalence to translate our false assumption `modInv p y = 0`
  have h_iff := @modInv_eq_zero_iff p hFact y
  have h_zero : (y : ZMod p) = 0 := h_iff.mp h
  -- Now assert that `(y : ZMod p) ≠ 0` based on our boundary constraints
  have h_ne_zero : (y : ZMod p) ≠ 0 := zmod_cast_ne_zero p y hy1 hyp
  -- Derive the contradiction
  exact h_ne_zero h_zero

theorem modInv_pos (p : ℕ) (hp_prime : p.Prime) (y : ℕ) (hy1 : 1 ≤ y) (hyp : y < p) :
  1 ≤ modInv p y :=
by
  have h := modInv_ne_zero p hp_prime y hy1 hyp
  omega

theorem modInv_lt_p_custom (p y : ℕ) (hp : p.Prime) : modInv p y < p :=
by
  -- Since p is prime, it is non-zero.
  -- We instantiate `NeZero p` which is required by `ZMod.val_lt`.
  haveI : NeZero p := ⟨hp.ne_zero⟩

  -- Apply the fact that the value of any element in ZMod p is strictly less than p.
  -- The elaborator automatically infers the element `(y : ZMod p)⁻¹` from the goal's definition.
  exact ZMod.val_lt _

theorem one_le_p_of_prime (p : ℕ) (hp : p.Prime) : 1 ≤ p :=
by
  have h := hp.one_lt
  omega

theorem cast_p_sub_one_eq_sub (p : ℕ) (hp : p.Prime) : ((p - 1 : ℕ) : ZMod p) = (p : ZMod p) - (1 : ZMod p) :=
by
  -- We apply `Nat.cast_sub`, giving it the proof that 1 ≤ p.
  -- This distributes the cast over the natural number subtraction.
  rw [Nat.cast_sub (one_le_p_of_prime p hp)]
  -- Simplify any remaining standard casts like `↑1` into `1` to automatically close the goal.
  simp

theorem coe_p_sub_one_eq_neg_one (p : ℕ) (hp : p.Prime) : ((p - 1 : ℕ) : ZMod p) = -1 :=
by
  rw [cast_p_sub_one_eq_sub p hp]
  rw [ZMod.natCast_self p]
  ring

theorem inv_neg_one_zmod (p : ℕ) (hp : p.Prime) : (-1 : ZMod p)⁻¹ = -1 :=
by
  haveI : Fact p.Prime := ⟨hp⟩
  exact inv_neg_one

theorem ZMod_neg_val_custom' (p : ℕ) (hp : p.Prime) {a : ZMod p} (ha : a ≠ 0) :
  ZMod.val (-a) = p - ZMod.val a :=
by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  rw [ZMod.neg_val, if_neg ha]

theorem prime_ne_one_custom (p : ℕ) (hp : p.Prime) : p ≠ 1 :=
hp.ne_one

theorem zmod_one_eq_natCast (p : ℕ) : (1 : ZMod p) = ((1 : ℕ) : ZMod p) :=
by
  exact Nat.cast_one.symm

theorem natCast_one_eq_zero_iff_dvd (p : ℕ) : ((1 : ℕ) : ZMod p) = 0 ↔ p ∣ 1 :=
by
  exact CharP.cast_eq_zero_iff (ZMod p) p 1

theorem zmod_one_eq_zero_iff_custom (p : ℕ) : (1 : ZMod p) = 0 ↔ p = 1 :=
by
  rw [zmod_one_eq_natCast p]
  rw [natCast_one_eq_zero_iff_dvd p]
  exact Nat.dvd_one

theorem one_ne_zero_of_prime (p : ℕ) (hp : p.Prime) : (1 : ZMod p) ≠ 0 :=
by
  intro h
  have h1 : p = 1 := (zmod_one_eq_zero_iff_custom p).mp h
  exact prime_ne_one_custom p hp h1

theorem val_one_eq_one_of_prime (p : ℕ) (hp : p.Prime) : ZMod.val (1 : ZMod p) = 1 :=
by
  exact ZMod.val_one'' hp.ne_one

theorem neg_one_eq_neg_one_val (p : ℕ) : (-1 : ZMod p) = -(1 : ZMod p) :=
rfl

theorem val_neg_one_eq_p_sub_one (p : ℕ) (hp : p.Prime) : ZMod.val (-1 : ZMod p) = p - 1 :=
by
  -- 1. Fulfill typeclass requirement for NeZero p (required logically by context limits)
  haveI : NeZero p := ⟨hp.ne_zero⟩

  -- 2. Recognize that -1 is definitionally the additive inverse of 1 in ZMod p
  rw [neg_one_eq_neg_one_val p]

  -- 3. Unfold negation using the conditional branch (since 1 ≠ 0, it resolves to p - ZMod.val 1)
  rw [ZMod_neg_val_custom' p hp (one_ne_zero_of_prime p hp)]

  -- 4. Substitute the canonical value of 1 in ZMod p
  rw [val_one_eq_one_of_prime p hp]

  -- The goal dynamically simplifies exactly to `p - 1 = p - 1`, resolving the proof automatically via `rfl`

theorem modInv_p_sub_one_custom (p : ℕ) (hp : p.Prime) : modInv p (p - 1) = p - 1 :=
by
  unfold modInv
  have h1 : ((p - 1 : ℕ) : ZMod p) = -1 := coe_p_sub_one_eq_neg_one p hp
  have h2 : (-1 : ZMod p)⁻¹ = -1 := inv_neg_one_zmod p hp
  have h3 : ZMod.val (-1 : ZMod p) = p - 1 := val_neg_one_eq_p_sub_one p hp
  rw [h1, h2, h3]

theorem natCast_val_eq_custom {p : ℕ} (hp : p.Prime) (x : ZMod p) : (ZMod.val x : ZMod p) = x :=
by
  -- Provide the instance that p is not zero, which is required by `ZMod.natCast_zmod_val`
  haveI : NeZero p := ⟨hp.ne_zero⟩
  exact ZMod.natCast_zmod_val x

theorem inv_inv_eq_custom {p : ℕ} (hp : p.Prime) (x : ZMod p) : (x⁻¹)⁻¹ = x :=
by
  haveI : Fact p.Prime := ⟨hp⟩
  exact inv_inv x

theorem val_natCast_of_lt_custom {p y : ℕ} (hy : y < p) : ZMod.val (y : ZMod p) = y :=
by
  exact ZMod.val_natCast_of_lt hy

theorem modInv_modInv_of_lt_p_custom (p y : ℕ) (hp : p.Prime) (hy : y < p) : modInv p (modInv p y) = y :=
by
  -- Unfold the definition of modInv to expose the underlying ZMod field operations.
  unfold modInv
  -- Rewrite the inner casting of the inverse back to ZMod p
  rw [natCast_val_eq_custom hp]
  -- Simplify the double inverse since ZMod p is a field when p is prime
  rw [inv_inv_eq_custom hp]
  -- Deduce that ZMod.val returns the original natural number when y < p
  rw [val_natCast_of_lt_custom hy]

theorem modInv_le_p_sub_two (p : ℕ) (hp_prime : p.Prime) (y : ℕ) (hy1 : 1 ≤ y) (hy2 : y ≤ p - 2) :
  modInv p y ≤ p - 2 :=
by
  -- Initial bounding derivations
  have hy_lt_p : y < p := by omega
  have h1 : modInv p y < p := modInv_lt_p_custom p y hp_prime

  -- Proceed by contradiction
  by_contra h_contra
  -- If it's strictly greater than p - 2 but less than p, it must be exactly p - 1
  have h_eq : modInv p y = p - 1 := by omega

  -- Apply our helper lemma safely via explicit parameters
  have h_inv_inv := modInv_modInv_of_lt_p_custom p y hp_prime hy_lt_p

  -- Substitute our contradictory assumption into the involution property
  rw [h_eq] at h_inv_inv

  -- Simplify using our auxiliary sub-problem
  have h_sub_one := modInv_p_sub_one_custom p hp_prime
  rw [h_sub_one] at h_inv_inv

  -- `h_inv_inv` now evaluates to `p - 1 = y`, directly contradicting `hy2 : y ≤ p - 2`.
  omega

theorem f_maps_Icc (p : ℕ) (hp_prime : p.Prime) (y : ℕ) (hy : y ∈ Finset.Icc 1 (p - 2)) :
  modInv p y + 1 ∈ Finset.Icc 2 (p - 1) :=
by
  rw [Finset.mem_Icc] at hy ⊢
  have hp2 : 2 ≤ p := hp_prime.two_le
  have hyp : y < p := by omega
  have h1 := modInv_pos p hp_prime y hy.1 hyp
  have h2 := modInv_le_p_sub_two p hp_prime y hy.1 hy.2
  constructor
  · omega
  · omega

theorem toNat_sub_one_pos_of_ge_two (u : ℕ) (hu : 2 ≤ u) : 1 ≤ Int.toNat ((u : ℤ) - 1) :=
by
  omega

theorem modInv_pos_aux (p : ℕ) (hp_prime : p.Prime) (u : ℕ) (hu : u ∈ Finset.Icc 2 (p - 1)) :
  1 ≤ modInv p (Int.toNat ((u : ℤ) - 1)) :=
by
  -- 1. Extract the lower and upper bounds for `u` from the hypothesis `hu`
  have h_mem := Finset.mem_Icc.mp hu
  have hu2 : 2 ≤ u := h_mem.1

  -- 2. Establish the lower positivity bound of the evaluation
  have hy1 : 1 ≤ Int.toNat ((u : ℤ) - 1) := toNat_sub_one_pos_of_ge_two u hu2

  -- 3. Establish the strict upper bound dynamically
  have hyp : Int.toNat ((u : ℤ) - 1) < p := by
    have hp2 : 2 ≤ p := hp_prime.two_le
    have hu_ub := h_mem.2
    omega

  -- 4. Apply the explicitly stated modular inverse lemma with the constructed boundaries
  exact modInv_pos p hp_prime (Int.toNat ((u : ℤ) - 1)) hy1 hyp

theorem u_le_p_sub_one_int (p : ℕ) (u : ℕ) (hu : u ∈ Finset.Icc 2 (p - 1)) :
  (u : ℤ) ≤ (p : ℤ) - 1 :=
by
  rw [Finset.mem_Icc] at hu
  omega

theorem p_ge_two_int (p : ℕ) (hp : p.Prime) :
  (2 : ℤ) ≤ (p : ℤ) :=
by
  have h := Nat.Prime.two_le hp
  omega

theorem u_ge_two_int (p : ℕ) (u : ℕ) (hu : u ∈ Finset.Icc 2 (p - 1)) :
  (2 : ℤ) ≤ (u : ℤ) :=
by
  rw [Finset.mem_Icc] at hu
  omega

theorem toNat_sub_one_le_p_sub_two (p : ℕ) (hp_prime : p.Prime) (u : ℕ) (hu : u ∈ Finset.Icc 2 (p - 1)) :
  Int.toNat ((u : ℤ) - 1) ≤ p - 2 :=
by
  have h1 := u_le_p_sub_one_int p u hu
  have h2 := p_ge_two_int p hp_prime
  have h3 := u_ge_two_int p u hu
  omega

theorem get_lower_bound_new (p : ℕ) (u : ℕ) (hu : u ∈ Finset.Icc 2 (p - 1)) :
  2 ≤ u :=
by
  rw [Finset.mem_Icc] at hu
  exact hu.1

theorem toNat_sub_one_pos_of_ge_two_new (u : ℕ) (hu : 2 ≤ u) :
  1 ≤ Int.toNat ((u : ℤ) - 1) :=
by
  omega

theorem neZero_of_prime_p (p : ℕ) (hp : p.Prime) : NeZero p :=
⟨hp.ne_zero⟩

theorem modInv_lt_p_of_prime (p : ℕ) (hp_prime : p.Prime) (y : ℕ) :
  modInv p y < p :=
by
  haveI : NeZero p := neZero_of_prime_p p hp_prime
  exact ZMod.val_lt ((y : ZMod p)⁻¹)

theorem zmod_eq_neg_one_of_val_add_one_eq_p (p : ℕ) [NeZero p] (x : ZMod p) (h : ZMod.val x + 1 = p) : x = -1 :=
by
  have h_eq : x + 1 = 0 := by
    calc
      x + 1 = (ZMod.val x : ZMod p) + 1 := by simp
      _ = ((ZMod.val x + 1 : ℕ) : ZMod p) := by push_cast; ring
      _ = (p : ZMod p) := by rw [h]
      _ = 0 := by simp
  calc
    x = (x + 1) - 1 := by ring
    _ = 0 - 1 := by rw [h_eq]
    _ = -1 := by ring

theorem zmod_eq_neg_one_of_modInv_add_one_eq_p (p : ℕ) (hp_prime : p.Prime) (y : ℕ) (hy : y < p) (h : modInv p y + 1 = p) : (y : ZMod p)⁻¹ = -1 :=
by
  haveI : NeZero p := neZero_of_prime_p p hp_prime
  exact zmod_eq_neg_one_of_val_add_one_eq_p p ((y : ZMod p)⁻¹) h

theorem zmod_eq_neg_one_of_inv_eq_neg_one (p : ℕ) (hp_prime : p.Prime) (y : ZMod p) (h : y⁻¹ = -1) : y = -1 :=
by
  haveI : Fact p.Prime := ⟨hp_prime⟩
  rw [← inv_inv y, h, inv_neg_one]

theorem zmod_eq_neg_one_iff_add_one_eq_zero (p y : ℕ) :
  (y : ZMod p) = -1 ↔ ((y + 1 : ℕ) : ZMod p) = 0 :=
by
  constructor
  · intro h
    push_cast
    rw [h]
    ring
  · intro h
    push_cast at h
    calc (y : ZMod p) = ((y : ZMod p) + 1) - 1 := by ring
      _ = (0 : ZMod p) - 1 := by rw [h]
      _ = -1 := by ring

theorem natCast_zmod_eq_zero_iff_dvd (p n : ℕ) :
  (n : ZMod p) = 0 ↔ p ∣ n :=
by
  exact ZMod.natCast_eq_zero_iff n p

theorem zmod_eq_neg_one_iff_dvd_add_one (p y : ℕ) : (y : ZMod p) = -1 ↔ p ∣ y + 1 :=
Iff.trans (zmod_eq_neg_one_iff_add_one_eq_zero p y) (natCast_zmod_eq_zero_iff_dvd p (y + 1))

theorem nat_eq_of_dvd_of_bounds (p x : ℕ) (hx_pos : 0 < x) (hx_le : x ≤ p) (h_dvd : p ∣ x) : x = p :=
by
  have h_le : p ≤ x := Nat.le_of_dvd hx_pos h_dvd
  exact le_antisymm hx_le h_le

theorem nat_add_one_eq_p_of_zmod_eq_neg_one (p : ℕ) (hp_prime : p.Prime) (y : ℕ) (hy : y < p) (h : (y : ZMod p) = -1) : y + 1 = p :=
by
  have h_dvd : p ∣ y + 1 := (zmod_eq_neg_one_iff_dvd_add_one p y).mp h
  have h_pos : 0 < y + 1 := by omega
  have h_le : y + 1 ≤ p := by omega
  exact nat_eq_of_dvd_of_bounds p (y + 1) h_pos h_le h_dvd

theorem eq_p_sub_one_of_modInv_eq (p : ℕ) (hp_prime : p.Prime) (y : ℕ) (hy : y < p)
  (h : modInv p y + 1 = p) : y + 1 = p :=
by
  have h1 : ((y : ZMod p)⁻¹) = -1 := zmod_eq_neg_one_of_modInv_add_one_eq_p p hp_prime y hy h
  have h2 : (y : ZMod p) = -1 := zmod_eq_neg_one_of_inv_eq_neg_one p hp_prime (y : ZMod p) h1
  exact nat_add_one_eq_p_of_zmod_eq_neg_one p hp_prime y hy h2

theorem modInv_le_p_sub_two_new (p : ℕ) (hp_prime : p.Prime) (y : ℕ) (hy1 : 1 ≤ y) (hy2 : y ≤ p - 2) :
  modInv p y ≤ p - 2 :=
by
  have h1 : modInv p y < p := modInv_lt_p_of_prime p hp_prime y
  have hy : y < p := by omega
  by_contra h
  have h2 : modInv p y + 1 = p := by omega
  have h3 : y + 1 = p := eq_p_sub_one_of_modInv_eq p hp_prime y hy h2
  omega

theorem modInv_le_p_sub_two_aux (p : ℕ) (hp_prime : p.Prime) (u : ℕ) (hu : u ∈ Finset.Icc 2 (p - 1)) :
  modInv p (Int.toNat ((u : ℤ) - 1)) ≤ p - 2 :=
modInv_le_p_sub_two_new p hp_prime (Int.toNat ((u : ℤ) - 1))
    (toNat_sub_one_pos_of_ge_two_new u (get_lower_bound_new p u hu))
    (toNat_sub_one_le_p_sub_two p hp_prime u hu)

theorem g_maps_Icc (p : ℕ) (hp_prime : p.Prime) (u : ℕ) (hu : u ∈ Finset.Icc 2 (p - 1)) :
  modInv p (Int.toNat ((u : ℤ) - 1)) ∈ Finset.Icc 1 (p - 2) :=
Finset.mem_Icc.mpr ⟨modInv_pos_aux p hp_prime u hu, modInv_le_p_sub_two_aux p hp_prime u hu⟩

theorem get_lower_bound (p : ℕ) (u : ℕ) (hu : u ∈ Finset.Icc 2 (p - 1)) : 2 ≤ u :=
(Finset.mem_Icc.mp hu).1

theorem toNat_sub_one_lt_p (p : ℕ) (u : ℕ) (hu : u ∈ Finset.Icc 2 (p - 1)) :
  Int.toNat ((u : ℤ) - 1) < p :=
by
  rw [Finset.mem_Icc] at hu
  omega

theorem toNat_sub_one_add_one (u : ℕ) (hu : 2 ≤ u) :
  Int.toNat ((u : ℤ) - 1) + 1 = u :=
by
  omega

theorem modInv_def (p k : ℕ) : modInv p k = ZMod.val (k : ZMod p)⁻¹ :=
rfl

theorem ZMod_val_natCast_eq (p k : ℕ) (hk : k < p) : ZMod.val (k : ZMod p) = k :=
ZMod.val_cast_of_lt hk

theorem coe_modInv (p k : ℕ) [Fact p.Prime] : (modInv p k : ZMod p) = (k : ZMod p)⁻¹ :=
by
  exact ZMod.natCast_zmod_val ((k : ZMod p)⁻¹)

theorem modInv_modInv_of_lt_p (p : ℕ) [Fact p.Prime] (k : ℕ) (hk : k < p) :
  modInv p (modInv p k) = k :=
by
  -- 1. Unfold the outer modInv operation using its definition
  rw [modInv_def p (modInv p k)]

  -- 2. Coerce the inner modInv computation back into the field ZMod p
  rw [coe_modInv p k]

  -- 3. In a field ZMod p, the inverse is an involution, so x⁻¹⁻¹ = x
  rw [inv_inv]

  -- 4. Extract the canonical integer representative, which is just k since k < p
  rw [ZMod_val_natCast_eq p k hk]

theorem f_g_inv (p : ℕ) (hp_prime : p.Prime) (u : ℕ) (hu : u ∈ Finset.Icc 2 (p - 1)) :
  modInv p (modInv p (Int.toNat ((u : ℤ) - 1))) + 1 = u :=
by
  -- 1. Register the primality of p as a class instance for modulo operations
  haveI : Fact p.Prime := ⟨hp_prime⟩

  -- 2. Validate that our target element `u - 1` maps below `p`
  have hk : Int.toNat ((u : ℤ) - 1) < p := toNat_sub_one_lt_p p u hu

  -- 3. Apply the involution property of the modular inversion for values under `p`
  rw [modInv_modInv_of_lt_p p (Int.toNat ((u : ℤ) - 1)) hk]

  -- 4. Establish the lower bound naturally mapping `u`
  have hu_bounds : 2 ≤ u := get_lower_bound p u hu

  -- 5. Close the goal by simplifying the integer mapping addition back into the natural number `u`
  exact toNat_sub_one_add_one u hu_bounds

theorem Int_toNat_add_one_sub_one (k : ℕ) :
  Int.toNat (((k + 1 : ℕ) : ℤ) - 1) = k :=
by
  omega

theorem y_lt_p_of_mem_Icc (p y : ℕ) (hp_prime : p.Prime) (hy : y ∈ Finset.Icc 1 (p - 2)) :
  y < p :=
by
  -- Extract bounds from the interval membership
  rw [Finset.mem_Icc] at hy

  -- Since p is prime, it must be at least 2
  have hp2 : 2 ≤ p := hp_prime.two_le

  -- Use omega to handle the natural number arithmetic and subtraction logic
  omega

theorem modInv_unfold (p k : ℕ) : modInv p k = ZMod.val (k : ZMod p)⁻¹ :=
rfl

theorem zmod_zero_inv_zero : ((0 : ℕ) : ZMod 0)⁻¹ = (0 : ZMod 0) :=
rfl

theorem zmod_zero_inv_succ (n : ℕ) : ((Nat.succ n : ℕ) : ZMod 0)⁻¹ = (1 : ZMod 0) :=
rfl

theorem zmod_inv_zero_or_one (k : ℕ) : (k : ZMod 0)⁻¹ = (0 : ZMod 0) ∨ (k : ZMod 0)⁻¹ = (1 : ZMod 0) :=
by
  cases k with
  | zero =>
    left
    exact zmod_zero_inv_zero
  | succ n =>
    right
    exact zmod_zero_inv_succ n

theorem zmod_val_zero_eq : (ZMod.val (0 : ZMod 0) : ZMod 0) = (0 : ZMod 0) :=
rfl

theorem zmod_val_one_eq : (ZMod.val (1 : ZMod 0) : ZMod 0) = (1 : ZMod 0) :=
rfl

theorem modInv_coe_zmod_zero (k : ℕ) :
  (ZMod.val (k : ZMod 0)⁻¹ : ZMod 0) = (k : ZMod 0)⁻¹ :=
by
  obtain h | h := zmod_inv_zero_or_one k
  · rw [h, zmod_val_zero_eq]
  · rw [h, zmod_val_one_eq]

theorem modInv_val_lt_succ (p k : ℕ) : ZMod.val ((k : ZMod (p + 1))⁻¹) < p + 1 :=
by
  exact ZMod.val_lt ((k : ZMod (p + 1))⁻¹)

theorem zmod_cast_of_val_eq_of_lt (p : ℕ) (v : ℕ) (x : ZMod (p + 1)) (h_lt : v < p + 1) (h : ZMod.val x = v) :
  (v : ZMod (p + 1)) = x :=
by
  rw [← h]
  exact ZMod.natCast_zmod_val x

theorem modInv_coe_zmod_succ (p k : ℕ) :
  (ZMod.val (k : ZMod (p + 1))⁻¹ : ZMod (p + 1)) = (k : ZMod (p + 1))⁻¹ :=
by
  have h_lt := modInv_val_lt_succ p k
  have h_eq : ZMod.val ((k : ZMod (p + 1))⁻¹) = ZMod.val ((k : ZMod (p + 1))⁻¹) := rfl
  exact zmod_cast_of_val_eq_of_lt p _ _ h_lt h_eq

theorem modInv_coe_zmod (p k : ℕ) :
  (modInv p k : ZMod p) = (k : ZMod p)⁻¹ :=
by
  rw [modInv_unfold]
  cases p with
  | zero =>
    exact modInv_coe_zmod_zero k
  | succ p' =>
    exact modInv_coe_zmod_succ p' k

theorem natCast_mod_p_eq (p y : ℕ) : ZMod.val (y : ZMod p) = ZMod.val ((y % p) : ZMod p) :=
by
  exact congrArg ZMod.val (ZMod.natCast_mod y p).symm

theorem val_natCast_mod_eq (p y : ℕ) : ZMod.val ((y % p) : ZMod p) = y % p :=
by
  rw [ZMod.val_natCast, Nat.mod_mod]

theorem val_natCast_eq_mod_p (p y : ℕ) : ZMod.val (y : ZMod p) = y % p :=
by
  rw [natCast_mod_p_eq p y]
  rw [val_natCast_mod_eq p y]

theorem mod_eq_self_of_lt {p y : ℕ} (hy : y < p) : y % p = y :=
Nat.mod_eq_of_lt hy

theorem val_natCast_of_lt {p y : ℕ} (hy : y < p) :
  ZMod.val (y : ZMod p) = y :=
by
  rw [val_natCast_eq_mod_p p y]
  rw [mod_eq_self_of_lt hy]

theorem my_modInv_modInv (p y : ℕ) (hp_prime : p.Prime) (hy : y < p) :
  modInv p (modInv p y) = y :=
by
  haveI : Fact p.Prime := ⟨hp_prime⟩
  rw [modInv_unfold p (modInv p y)]
  rw [modInv_coe_zmod p y]
  rw [inv_inv]
  rw [val_natCast_of_lt hy]

theorem g_f_inv (p : ℕ) (hp_prime : p.Prime) (y : ℕ) (hy : y ∈ Finset.Icc 1 (p - 2)) :
  modInv p (Int.toNat (((modInv p y + 1 : ℕ) : ℤ) - 1)) = y :=
by
  -- Simplify the algebraic structure of the inner arithmetic expression
  rw [Int_toNat_add_one_sub_one]

  -- Apply the involution property using our bounded lemma for its prerequisite
  exact my_modInv_modInv p y hp_prime (y_lt_p_of_mem_Icc p y hp_prime hy)

theorem y_bounds_of_mem_Icc (p y : ℕ) [Fact p.Prime] (hy : y ∈ Finset.Icc 1 (p - 2)) : 0 < y ∧ y < p :=
by
  -- Extract the inequalities from the interval membership
  rw [Finset.mem_Icc] at hy

  -- Extract the property that p is prime, which implies p ≥ 2
  have hp : p.Prime := Fact.out
  have hp2 : 2 ≤ p := hp.two_le

  -- Use omega to handle the natural number arithmetic naturally
  omega

theorem int_le_of_dvd_and_pos (p y : ℤ) (hy : 0 < y) (h_dvd : p ∣ y) : p ≤ y :=
by
  have hne : y ≠ 0 := by omega
  have h := Int.le_abs_of_dvd hne h_dvd
  rw [abs_of_pos hy] at h
  exact h

theorem int_dvd_contradiction (p y : ℤ) (h1 : 0 < y) (h2 : y < p) (h3 : p ∣ y) : False :=
by
  have h4 := int_le_of_dvd_and_pos p y h1 h3
  omega

theorem y_cast_ne_zero (p : ℕ) [Fact p.Prime] (y : ℕ) (hy : y ∈ Finset.Icc 1 (p - 2)) :
  (y : ZMod p) ≠ 0 :=
by
  intro h

  -- Extract bounds for y based on interval membership
  have h_bound : 0 < y ∧ y < p := y_bounds_of_mem_Icc p y hy
  have h_bound_left : 0 < y := h_bound.1
  have h_bound_right : y < p := h_bound.2

  -- Step 1: Cast the assumption to the integers in ZMod p
  have h_int_cast : ((y : ℤ) : ZMod p) = 0 := by
    calc
      ((y : ℤ) : ZMod p) = (y : ZMod p) := by push_cast; rfl
      _ = 0 := h

  -- Step 2: Utilize the Mathlib equivalence `ZMod.intCast_zmod_eq_zero_iff_dvd` to transition to integer divisibility
  have h_dvd : (p : ℤ) ∣ (y : ℤ) := (ZMod.intCast_zmod_eq_zero_iff_dvd (y : ℤ) p).mp h_int_cast

  -- Step 3: Shift the bounds extracted earlier safely into Int (ℤ)
  have h1 : 0 < (y : ℤ) := by omega
  have h2 : (y : ℤ) < (p : ℤ) := by omega

  -- Step 4: Arrive at the contradiction! (A strictly smaller positive integer cannot be a multiple of a larger one)
  exact int_dvd_contradiction (p : ℤ) (y : ℤ) h1 h2 h_dvd

theorem p_pos_of_hy (p y : ℕ) (hy : y ∈ Finset.Icc 1 (p - 2)) : 0 < p :=
by
  rw [Finset.mem_Icc] at hy
  omega

theorem y_add_one_lt_p_of_hy (p y : ℕ) (hy : y ∈ Finset.Icc 1 (p - 2)) : y + 1 < p :=
by
  rw [Finset.mem_Icc] at hy
  omega

theorem y_add_one_eq_cast_add_one (p y : ℕ) : (y : ZMod p) + 1 = ((y + 1 : ℕ) : ZMod p) :=
by
  push_cast
  rfl

theorem cast_zero_eq_zero (p : ℕ) : (0 : ZMod p) = ((0 : ℕ) : ZMod p) :=
by
  exact Nat.cast_zero.symm

theorem y_ge_one_of_hy (p y : ℕ) (hy : y ∈ Finset.Icc 1 (p - 2)) : 1 ≤ y :=
by
  rw [Finset.mem_Icc] at hy
  exact hy.1

theorem y_add_one_cast_ne_zero (p : ℕ) [Fact p.Prime] (y : ℕ) (hy : y ∈ Finset.Icc 1 (p - 2)) :
  (y : ZMod p) + 1 ≠ 0 :=
by
  -- Assume for contradiction that (y : ZMod p) + 1 = 0
  intro h

  -- Extract integer bounds based on the interval hypothesis
  have hp : 0 < p := p_pos_of_hy p y hy
  have h_lt : y + 1 < p := y_add_one_lt_p_of_hy p y hy

  -- Shift the arithmetic out of modulo constraints to natural number casts
  rw [y_add_one_eq_cast_add_one p y] at h
  rw [cast_zero_eq_zero p] at h

  -- Apply the canonical representative mapping `ZMod.val` to both sides
  have h_val := congrArg ZMod.val h

  -- Evaluate `ZMod.val` specifically for expressions that have not wrapped around the modulus `p`
  rw [val_natCast_of_lt h_lt] at h_val
  rw [val_natCast_of_lt hp] at h_val

  -- Resolve the evident arithmetical contradiction: y + 1 = 0 while 1 ≤ y
  have hy1 : 1 ≤ y := y_ge_one_of_hy p y hy
  omega

theorem inv_eq_neg_one_iff {F : Type*} [DivisionRing F] (x : F) : x⁻¹ = -1 ↔ x = -1 :=
by
  rw [inv_eq_iff_eq_inv, inv_neg_one]

theorem inv_add_one_eq_zero_iff {F : Type*} [DivisionRing F] (x : F) :
  x⁻¹ + 1 = 0 ↔ x + 1 = 0 :=
by
  constructor
  · intro h
    rw [add_eq_zero_iff_neg_eq'] at h
    rw [add_eq_zero_iff_neg_eq']
    exact ((inv_eq_neg_one_iff x).mp h.symm).symm
  · intro h
    rw [add_eq_zero_iff_neg_eq'] at h
    rw [add_eq_zero_iff_neg_eq']
    exact ((inv_eq_neg_one_iff x).mpr h.symm).symm

theorem inv_add_one_ne_zero (p : ℕ) [Fact p.Prime] (y : ℕ) (hy : y ∈ Finset.Icc 1 (p - 2)) :
  (y : ZMod p)⁻¹ + 1 ≠ 0 :=
by
  intro h
  have h2 : (y : ZMod p) + 1 = 0 := (inv_add_one_eq_zero_iff (y : ZMod p)).mp h
  exact y_add_one_cast_ne_zero p y hy h2

theorem modInv_add_modInv_zmod_eq_one (p : ℕ) [Fact p.Prime] (y : ℕ) (hy : y ∈ Finset.Icc 1 (p - 2)) :
  ((modInv p (y + 1) : ZMod p) + (modInv p (modInv p y + 1) : ZMod p)) = 1 :=
by
  have h1 : (y : ZMod p) ≠ 0 := y_cast_ne_zero p y hy
  have h2 : (y : ZMod p) + 1 ≠ 0 := y_add_one_cast_ne_zero p y hy
  have h3 : (y : ZMod p)⁻¹ + 1 ≠ 0 := inv_add_one_ne_zero p y hy

  -- field_simp generates fractions with denominators `1 + y` and `1 + y⁻¹`.
  -- We provide them explicitly so it doesn't get stuck trying to clear them.
  have h4 : 1 + (y : ZMod p) ≠ 0 := by
    rw [add_comm]
    exact h2
  have h5 : 1 + (y : ZMod p)⁻¹ ≠ 0 := by
    rw [add_comm]
    exact h3

  rw [modInv_coe_zmod p (y + 1), modInv_coe_zmod p (modInv p y + 1)]
  push_cast
  rw [modInv_coe_zmod p y]

  -- Now field_simp will have all the necessary non-zero facts to clear ALL denominators
  field_simp [h1, h2, h3, h4, h5]
  ring

theorem dvd_sub_one_of_zmod_eq_one (p : ℕ) (S : ℤ) (h : (S : ZMod p) = 1) :
  (p : ℤ) ∣ S - 1 :=
by
  -- Use the equivalence `↑a = ↑b ↔ ↑p ∣ b - a` for `a = 1` and `b = S`.
  apply (ZMod.intCast_eq_intCast_iff_dvd_sub (1 : ℤ) S p).mp
  -- We are left to show `((1 : ℤ) : ZMod p) = (S : ZMod p)`
  rw [Int.cast_one]
  -- Which is exactly `1 = (S : ZMod p)`, the symmetry of our hypothesis
  exact h.symm

theorem y_add_one_bounds (p : ℕ) (y : ℕ) (hy : y ∈ Finset.Icc 1 (p - 2)) :
  1 ≤ y + 1 ∧ y + 1 < p :=
by
  simp only [Finset.mem_Icc] at hy
  omega

theorem modInv_y_add_one_bounds (p : ℕ) (hp_prime : p.Prime) (y : ℕ) (hy : y ∈ Finset.Icc 1 (p - 2)) :
  1 ≤ modInv p y + 1 ∧ modInv p y + 1 < p :=
by
  have hy' := Finset.mem_Icc.mp hy
  have h_inv_le := modInv_le_p_sub_two p hp_prime y hy'.1 hy'.2
  omega

theorem modInv_sum_ge_two (p : ℕ) (hp_prime : p.Prime) (y : ℕ) (hy : y ∈ Finset.Icc 1 (p - 2)) :
  2 ≤ ((modInv p (y + 1) : ℕ) : ℤ) + ((modInv p (modInv p y + 1) : ℕ) : ℤ) :=
by
  -- Obtain bounds for the arguments of modInv
  have h1 := y_add_one_bounds p y hy
  have h3 := modInv_y_add_one_bounds p hp_prime y hy

  -- Use the established bounds with modInv_pos to get that both inverses are at least 1
  have h2 := modInv_pos p hp_prime (y + 1) h1.1 h1.2
  have h4 := modInv_pos p hp_prime (modInv p y + 1) h3.1 h3.2

  -- omega easily deduces that 2 ≤ a + b over integers given 1 ≤ a and 1 ≤ b in naturals
  omega

theorem modInv_lt (p : ℕ) [Fact p.Prime] (k : ℕ) : modInv p k < p :=
by
  haveI : NeZero p := ⟨by
    have h : 1 < p := (Fact.out : p.Prime).one_lt
    omega⟩
  exact ZMod.val_lt ((k : ZMod p)⁻¹)

theorem modInv_le_int (p : ℕ) [Fact p.Prime] (k : ℕ) : (modInv p k : ℤ) ≤ (p : ℤ) - 1 :=
by
  have h := modInv_lt p k
  omega

theorem modInv_sum_le_two_p_sub_two (p : ℕ) [Fact p.Prime] (y : ℕ) :
  ((modInv p (y + 1) : ℕ) : ℤ) + ((modInv p (modInv p y + 1) : ℕ) : ℤ) ≤ 2 * (p : ℤ) - 2 :=
by
  have h1 := modInv_le_int p (y + 1)
  have h2 := modInv_le_int p (modInv p y + 1)
  linarith

theorem int_eq_p_add_one_of_dvd_helper_k_pos (p S k : ℤ) (hp : 0 < p) (hk : S - 1 = p * k) (h2 : 2 ≤ S) :
  0 < k :=
by
  nlinarith

theorem int_eq_p_add_one_of_dvd_helper_k_lt_two (p S k : ℤ) (hp : 0 < p) (hk : S - 1 = p * k) (h3 : S ≤ 2 * p - 2) :
  k < 2 :=
by
  nlinarith

theorem int_eq_p_add_one_of_dvd_helper (p S k : ℤ) (hp : 0 < p) (hk : S - 1 = p * k) (h2 : 2 ≤ S) (h3 : S ≤ 2 * p - 2) :
  k = 1 :=
by
  have h_pos : 0 < k := int_eq_p_add_one_of_dvd_helper_k_pos p S k hp hk h2
  have h_lt : k < 2 := int_eq_p_add_one_of_dvd_helper_k_lt_two p S k hp hk h3
  omega

theorem int_eq_p_add_one_of_dvd (p : ℕ) (S : ℤ) (hp : 0 < (p : ℤ)) (h1 : (p : ℤ) ∣ S - 1) (h2 : 2 ≤ S) (h3 : S ≤ 2 * (p : ℤ) - 2) :
  S = (p : ℤ) + 1 :=
by
  rcases h1 with ⟨k, hk⟩
  have hk_eq_one : k = 1 := int_eq_p_add_one_of_dvd_helper (p : ℤ) S k hp hk h2 h3
  rw [hk_eq_one] at hk
  omega

theorem prime_pos_int (p : ℕ) (hp : p.Prime) : 0 < (p : ℤ) :=
by
  have h := hp.pos
  omega

theorem lemma_modInv_sum_eq (p : ℕ) (hp_prime : p.Prime) (y : ℕ) (hy : y ∈ Finset.Icc 1 (p - 2)) :
  ((modInv p (y + 1) : ℕ) : ℤ) + ((modInv p (modInv p y + 1) : ℕ) : ℤ) = (p : ℤ) + 1 :=
by
  haveI : Fact p.Prime := ⟨hp_prime⟩

  -- Step 1: Prove the evaluation of the sum modulo p
  have h_zmod : ((((modInv p (y + 1) : ℕ) : ℤ) + ((modInv p (modInv p y + 1) : ℕ) : ℤ) : ℤ) : ZMod p) = 1 := by
    push_cast
    exact modInv_add_modInv_zmod_eq_one p y hy

  -- Step 2: Extract the divisibility relationship in integers
  have h_dvd : (p : ℤ) ∣ (((modInv p (y + 1) : ℕ) : ℤ) + ((modInv p (modInv p y + 1) : ℕ) : ℤ)) - 1 :=
    dvd_sub_one_of_zmod_eq_one p (((modInv p (y + 1) : ℕ) : ℤ) + ((modInv p (modInv p y + 1) : ℕ) : ℤ)) h_zmod

  -- Step 3: Source the bounding limitations for the terms
  have h_ge : 2 ≤ ((modInv p (y + 1) : ℕ) : ℤ) + ((modInv p (modInv p y + 1) : ℕ) : ℤ) :=
    modInv_sum_ge_two p hp_prime y hy
  have h_le : ((modInv p (y + 1) : ℕ) : ℤ) + ((modInv p (modInv p y + 1) : ℕ) : ℤ) ≤ 2 * (p : ℤ) - 2 :=
    modInv_sum_le_two_p_sub_two p y

  -- Step 4: Supply required property limits and finalize the logical closure
  have hp_pos : 0 < (p : ℤ) :=
    prime_pos_int p hp_prime

  exact int_eq_p_add_one_of_dvd p (((modInv p (y + 1) : ℕ) : ℤ) + ((modInv p (modInv p y + 1) : ℕ) : ℤ)) hp_pos h_dvd h_ge h_le

theorem condition_equiv (p : ℕ) (hp_prime : p.Prime) (y : ℕ) (hy : y ∈ Finset.Icc 1 (p - 2)) :
  modInv p (y + 1) < modInv p y ↔
  (p : ℤ) + 3 ≤ ((modInv p y + 1 : ℕ) : ℤ) + ((modInv p (modInv p y + 1) : ℕ) : ℤ) :=
by
  have h := lemma_modInv_sum_eq p hp_prime y hy
  omega

theorem descent_count_eq_u_set (p : ℕ) (hp_prime : p.Prime) :
  descentCount p = (Finset.filter (fun (u : ℕ) => (p : ℤ) + 3 ≤ (u : ℤ) + (modInv p u : ℤ)) (Finset.Icc 2 (p - 1))).card :=
by
  rw [descentCount_eq p hp_prime]
  apply Set.BijOn.finsetCard_eq (fun (y : ℕ) => modInv p y + 1)
  refine ⟨?_, ?_, ?_⟩
  · intro y hy
    simp only [Finset.mem_coe, Finset.mem_filter] at hy ⊢
    rcases hy with ⟨hy_icc, hy_cond⟩
    refine ⟨f_maps_Icc p hp_prime y hy_icc, ?_⟩
    rw [← condition_equiv p hp_prime y hy_icc]
    exact hy_cond
  · intro a ha b hb hab
    simp only [Finset.mem_coe, Finset.mem_filter] at ha hb
    have ha_g := g_f_inv p hp_prime a ha.1
    have hb_g := g_f_inv p hp_prime b hb.1
    change modInv p a + 1 = modInv p b + 1 at hab
    have h_mod : modInv p a = modInv p b := by omega
    rw [h_mod] at ha_g
    exact ha_g.symm.trans hb_g
  · intro u hu
    simp only [Finset.mem_coe, Finset.mem_filter] at hu
    rcases hu with ⟨hu_icc, hu_cond⟩
    let a := modInv p (Int.toNat ((u : ℤ) - 1))
    have hg_icc : a ∈ Finset.Icc 1 (p - 2) := g_maps_Icc p hp_prime u hu_icc
    have hg_f : modInv p a + 1 = u := f_g_inv p hp_prime u hu_icc
    have hg_cond : modInv p (a + 1) < modInv p a := by
      rw [condition_equiv p hp_prime a hg_icc]
      have eq1 : ((modInv p a + 1 : ℕ) : ℤ) = (u : ℤ) := by rw [hg_f]
      have eq2 : ((modInv p (modInv p a + 1) : ℕ) : ℤ) = (modInv p u : ℤ) := by rw [hg_f]
      rw [eq1, eq2]
      exact hu_cond
    refine ⟨a, ?_, hg_f⟩
    simp only [Finset.mem_coe, Finset.mem_filter]
    exact ⟨hg_icc, hg_cond⟩

theorem p_minus_one_not_mem_J_set (p : ℕ) :
  p - 1 ∉ J_set p :=
by
  intro h
  unfold J_set at h
  simp only [Finset.mem_Icc, Finset.mem_Ico] at h
  omega

theorem p_minus_one_not_mem_D_J (p : ℕ) :
  p - 1 ∉ D_J p :=
by
  intro h
  unfold D_J at h
  rw [Finset.mem_filter] at h
  exact p_minus_one_not_mem_J_set p h.1

theorem Icc_2_p_minus_one_eq_insert (p : ℕ) (hp : p ≥ 11) :
  Finset.Icc 2 (p - 1) = insert (p - 1) (J_set p) :=
by
  ext x
  simp only [J_set, Finset.mem_Icc, Finset.mem_insert]
  omega

theorem modInv_def_lemma_for_p_minus_one (p u : ℕ) : modInv p u = ZMod.val ((u : ZMod p)⁻¹) :=
rfl

theorem prime_two_le_lemma_for_p_minus_one (p : ℕ) (hp : p.Prime) : 2 ≤ p :=
Nat.Prime.two_le hp

theorem one_le_p_of_two_le (p : ℕ) (hp : 2 ≤ p) : 1 ≤ p :=
by
  omega

theorem coe_p_minus_one_eq_sub (p : ℕ) (hp : 1 ≤ p) :
  ((p - 1 : ℕ) : ZMod p) = (p : ZMod p) - 1 :=
by
  rw [Nat.cast_sub hp, Nat.cast_one]

theorem coe_p_eq_zero (p : ℕ) : (p : ZMod p) = 0 :=
by
  exact ZMod.natCast_self p

theorem coe_p_minus_one (p : ℕ) (hp : 2 ≤ p) : ((p - 1 : ℕ) : ZMod p) = -1 :=
by
  have h1 := one_le_p_of_two_le p hp
  rw [coe_p_minus_one_eq_sub p h1]
  rw [coe_p_eq_zero p]
  exact zero_sub 1

theorem ZMod_inv_neg_one (p : ℕ) (hp_prime : p.Prime) : (-1 : ZMod p)⁻¹ = -1 :=
by
  haveI : Fact p.Prime := ⟨hp_prime⟩
  exact inv_neg_one

theorem val_neg_one (p : ℕ) (hp : 2 ≤ p) : ZMod.val (-1 : ZMod p) = p - 1 :=
by
  rw [← coe_p_minus_one p hp]
  exact ZMod.val_cast_of_lt (by omega)

theorem modInv_p_minus_one (p : ℕ) (hp_prime : p.Prime) :
  modInv p (p - 1) = p - 1 :=
by
  have hp : 2 ≤ p := prime_two_le_lemma_for_p_minus_one p hp_prime
  rw [modInv_def_lemma_for_p_minus_one]
  rw [coe_p_minus_one p hp]
  rw [ZMod_inv_neg_one p hp_prime]
  rw [val_neg_one p hp]

theorem filter_condition_p_minus_one (p : ℕ) (hp_prime : p.Prime) (hp : p ≥ 11) :
  (p : ℤ) + 3 ≤ ((p - 1 : ℕ) : ℤ) + (modInv p (p - 1) : ℤ) :=
by
  rw [modInv_p_minus_one p hp_prime]
  omega

theorem filter_insert_eq (p : ℕ) (hp_prime : p.Prime) (hp : p ≥ 11) :
  Finset.filter (fun (u : ℕ) => (p : ℤ) + 3 ≤ (u : ℤ) + (modInv p u : ℤ)) (insert (p - 1) (J_set p)) =
  insert (p - 1) (D_J p) :=
by
  -- Distribute the filter over the insertion operation
  rw [Finset.filter_insert]

  -- Evaluate the filter condition for the inserted element `p - 1`
  have h_cond : (p : ℤ) + 3 ≤ ((p - 1 : ℕ) : ℤ) + (modInv p (p - 1) : ℤ) :=
    filter_condition_p_minus_one p hp_prime hp

  -- Since the condition holds, simplify the if-then-else
  rw [if_pos h_cond]

  -- The remainder perfectly matches the mathematical definition of D_J p
  rfl

theorem u_set_eq_D_J_plus_one (p : ℕ) (hp_prime : p.Prime) (hp : p ≥ 11) :
  (Finset.filter (fun (u : ℕ) => (p : ℤ) + 3 ≤ (u : ℤ) + (modInv p u : ℤ)) (Finset.Icc 2 (p - 1))).card = (D_J p).card + 1 :=
by
  rw [Icc_2_p_minus_one_eq_insert p hp]
  rw [filter_insert_eq p hp_prime hp]
  exact Finset.card_insert_of_notMem (p_minus_one_not_mem_D_J p)

theorem le_of_mem_J_set (p u : ℕ) (hu : u ∈ J_set p) : u ≤ p :=
by
  simp only [J_set, Finset.mem_Icc, Finset.mem_Ico] at hu
  omega

theorem coe_symm_map (p u : ℕ) (h : u ≤ p) : (symm_map p u : ℤ) = (p : ℤ) - (u : ℤ) :=
by
  unfold symm_map
  omega

theorem symm_map_le (p u : ℕ) (h : u ≤ p) : symm_map p u ≤ p :=
by
  have h1 := coe_symm_map p u h
  omega

theorem symm_map_symm_map (p u : ℕ) (hu : u ∈ J_set p) :
  symm_map p (symm_map p u) = u :=
by
  have h1 : u ≤ p := le_of_mem_J_set p u hu
  have h2 : symm_map p u ≤ p := symm_map_le p u h1
  have h3 : (symm_map p (symm_map p u) : ℤ) = (p : ℤ) - (symm_map p u : ℤ) := coe_symm_map p (symm_map p u) h2
  have h4 : (symm_map p u : ℤ) = (p : ℤ) - (u : ℤ) := coe_symm_map p u h1
  omega

theorem mem_D_J_iff (p u : ℕ) :
  u ∈ D_J p ↔ u ∈ J_set p ∧ (p : ℤ) + 3 ≤ (u : ℤ) + (modInv p u : ℤ) :=
by
  unfold D_J
  rw [Finset.mem_filter]

theorem mem_J_set_of_mem_D_J (p u : ℕ) (hu : u ∈ D_J p) :
  u ∈ J_set p :=
by
  have h := (mem_D_J_iff p u).mp hu
  exact h.1

theorem bounds_of_mem_J_set (p u : ℕ) (hu : u ∈ J_set p) : 2 ≤ u ∧ u + 2 ≤ p :=
by
  unfold J_set at hu
  rw [Finset.mem_Icc] at hu
  constructor
  · omega
  · omega

theorem symm_map_ge_two (p u : ℕ) (hu : u ∈ J_set p) : 2 ≤ symm_map p u :=
by
  have ⟨h1, h2⟩ := bounds_of_mem_J_set p u hu
  have h3 : u ≤ p := by omega
  have h4 := coe_symm_map p u h3
  omega

theorem symm_map_le_p_minus_two (p u : ℕ) (hu : u ∈ J_set p) : symm_map p u ≤ p - 2 :=
by
  have h_bounds := bounds_of_mem_J_set p u hu
  have h_le : u ≤ p := by omega
  have h_coe := coe_symm_map p u h_le
  omega

theorem mem_J_set_of_bounds (p u : ℕ) (h1 : 2 ≤ u) (h2 : u ≤ p - 2) : u ∈ J_set p :=
by
  exact Finset.mem_Icc.mpr ⟨h1, h2⟩

theorem symm_map_mem_J_set (p u : ℕ) (hu : u ∈ J_set p) :
  symm_map p u ∈ J_set p :=
mem_J_set_of_bounds p (symm_map p u) (symm_map_ge_two p u hu) (symm_map_le_p_minus_two p u hu)

theorem zmod_symm_map_eq_neg (p u : ℕ) (h : u ≤ p) :
  (symm_map p u : ZMod p) = - (u : ZMod p) :=
by
  have h1 : (symm_map p u : ZMod p) = ((symm_map p u : ℤ) : ZMod p) := by push_cast; rfl
  rw [h1, coe_symm_map p u h]
  push_cast
  have hp : (p : ZMod p) = 0 := by simp
  rw [hp]
  ring

theorem dvd_of_zmod_eq_zero (p u : ℕ) (h : (u : ZMod p) = 0) : p ∣ u :=
by
  exact (CharP.cast_eq_zero_iff (ZMod p) p u).mp h

theorem zmod_eq_zero_of_dvd (p u : ℕ) (h : p ∣ u) : (u : ZMod p) = 0 :=
by
  rw [ZMod.natCast_eq_zero_iff]
  exact h

theorem zmod_u_eq_zero_iff_dvd (p u : ℕ) : (u : ZMod p) = 0 ↔ p ∣ u :=
by
  exact ⟨dvd_of_zmod_eq_zero p u, zmod_eq_zero_of_dvd p u⟩

theorem zmod_u_ne_zero (p u : ℕ) (hu : u ∈ J_set p) :
  (u : ZMod p) ≠ 0 :=
by
  intro h

  -- Rewrite the assumption into a divisibility condition
  have hdvd : p ∣ u := (zmod_u_eq_zero_iff_dvd p u).mp h

  -- Extract bounds from the J_set membership
  have ⟨h1, h2⟩ := bounds_of_mem_J_set p u hu

  -- Deduce strict bounds for `u` using omega
  have hy1 : 1 ≤ u := by omega
  have hyp : u < p := by omega

  -- Derive the contradiction
  have h_not_dvd := not_dvd_of_pos_of_lt p u hy1 hyp
  exact h_not_dvd hdvd

theorem inv_ne_zero_of_ne_zero (p : ℕ) (hp_prime : p.Prime) (x : ZMod p) (hx : x ≠ 0) :
  x⁻¹ ≠ 0 :=
by
  haveI : Fact p.Prime := ⟨hp_prime⟩
  exact inv_ne_zero hx

theorem zmod_inv_neg (p : ℕ) (hp_prime : p.Prime) (x : ZMod p) :
  (-x)⁻¹ = - (x⁻¹) :=
by
  haveI : Fact p.Prime := ⟨hp_prime⟩
  exact inv_neg

theorem zmod_val_neg_eq (p : ℕ) (hp_prime : p.Prime) (x : ZMod p) (hx : x ≠ 0) :
  (ZMod.val (-x) : ℤ) = (p : ℤ) - (ZMod.val x : ℤ) :=
by
  -- Obtain that p is at least 2 since it is prime, establishing p ≠ 0 for the ZMod context.
  have hp : 2 ≤ p := hp_prime.two_le
  haveI : NeZero p := ⟨by omega⟩

  -- Obtain the negation identity and bounding properties over the natural numbers
  have h1 := ZMod.neg_val x
  rw [if_neg hx] at h1
  have h2 := ZMod.val_lt x

  -- omega will correctly deduce the safe translation mapping subtraction into the integer domain
  omega

theorem modInv_symm_map_eq (p : ℕ) (hp_prime : p.Prime) (u : ℕ) (hu : u ∈ J_set p) :
  (modInv p (symm_map p u) : ℤ) = (p : ℤ) - (modInv p u : ℤ) :=
by
  have h1 : u ≤ p := le_of_mem_J_set p u hu
  have h3 : (u : ZMod p) ≠ 0 := zmod_u_ne_zero p u hu
  have h4 : (u : ZMod p)⁻¹ ≠ 0 := inv_ne_zero_of_ne_zero p hp_prime (u : ZMod p) h3

  -- Unfold `modInv` on the left hand side explicitly to expose the term to `rw`
  change (ZMod.val ((symm_map p u : ZMod p)⁻¹) : ℤ) = (p : ℤ) - (modInv p u : ℤ)

  rw [zmod_symm_map_eq_neg p u h1]
  rw [zmod_inv_neg p hp_prime (u : ZMod p)]

  -- This single rewrite yields `(p : ℤ) - (ZMod.val ((u : ZMod p)⁻¹) : ℤ)` matching the RHS.
  -- The `rw` tactic automatically applies `rfl` and successfully closes the goal definitionally
  -- since `modInv p u` is an `abbrev` for `ZMod.val ((u : ZMod p)⁻¹)`.
  rw [zmod_val_neg_eq p hp_prime ((u : ZMod p)⁻¹) h4]

theorem symm_map_add_modInv (p : ℕ) (hp_prime : p.Prime) (u : ℕ) (hu : u ∈ J_set p) :
  ((symm_map p u : ℤ) + (modInv p (symm_map p u) : ℤ)) = 2 * (p : ℤ) - ((u : ℤ) + (modInv p u : ℤ)) :=
by
  have h_le : u ≤ p := le_of_mem_J_set p u hu
  rw [coe_symm_map p u h_le]
  rw [modInv_symm_map_eq p hp_prime u hu]
  ring

theorem D_J_maps_to_B_J (p : ℕ) (hp_prime : p.Prime) :
  ∀ u ∈ D_J p, symm_map p u ∈ B_J p :=
by
  intro u hu
  -- Extract properties of u being in the J_set
  have hu_J : u ∈ J_set p := mem_J_set_of_mem_D_J p u hu
  have h_symm_J : symm_map p u ∈ J_set p := symm_map_mem_J_set p u hu_J

  -- The core algebraic identity from our auxiliary lemmas
  have h_add : ((symm_map p u : ℤ) + (modInv p (symm_map p u) : ℤ)) = 2 * (p : ℤ) - ((u : ℤ) + (modInv p u : ℤ)) :=
    symm_map_add_modInv p hp_prime u hu_J

  -- Unfold the definitions of D_J and B_J into their conditions
  simp only [D_J, B_J, Finset.mem_filter] at hu ⊢

  -- The target transforms into verifying membership in J_set (handled) and an inequality for B_J
  refine ⟨h_symm_J, ?_⟩

  -- Linear arithmetic is sufficient to finalize the bounding requirement:
  -- We know p + 3 ≤ u + modInv p u, thus 2p - (u + modInv p u) ≤ 2p - (p + 3) = p - 3.
  linarith

theorem mem_B_J_iff (p u : ℕ) :
  u ∈ B_J p ↔ u ∈ J_set p ∧ (u : ℤ) + (modInv p u : ℤ) ≤ (p : ℤ) - 3 :=
by
  exact Finset.mem_filter

theorem mem_J_set_of_mem_B_J (p u : ℕ) (hu : u ∈ B_J p) :
  u ∈ J_set p :=
by
  exact ((mem_B_J_iff p u).mp hu).1

theorem B_J_maps_to_D_J (p : ℕ) (hp_prime : p.Prime) :
  ∀ u ∈ B_J p, symm_map p u ∈ D_J p :=
by
  intro u hu
  have hu_J : u ∈ J_set p := mem_J_set_of_mem_B_J p u hu
  have h_symm_J : symm_map p u ∈ J_set p := symm_map_mem_J_set p u hu_J
  have h_B : (u : ℤ) + (modInv p u : ℤ) ≤ (p : ℤ) - 3 := ((mem_B_J_iff p u).mp hu).right
  have h_eq : ((symm_map p u : ℤ) + (modInv p (symm_map p u) : ℤ)) = 2 * (p : ℤ) - ((u : ℤ) + (modInv p u : ℤ)) :=
    symm_map_add_modInv p hp_prime u hu_J
  rw [mem_D_J_iff]
  exact ⟨h_symm_J, by linarith⟩

theorem card_nbij_helper {α β : Type*} (s : Finset α) (t : Finset β) (i : α → β) (j : β → α)
  (hi : ∀ a ∈ s, i a ∈ t)
  (hj : ∀ b ∈ t, j b ∈ s)
  (left_inv : ∀ a ∈ s, j (i a) = a)
  (right_inv : ∀ b ∈ t, i (j b) = b) : s.card = t.card :=
by
  exact Finset.card_nbij' i j hi hj left_inv right_inv

theorem D_J_B_J_symm (p : ℕ) (hp_prime : p.Prime) :
  (D_J p).card = (B_J p).card :=
by
  apply card_nbij_helper (D_J p) (B_J p) (symm_map p) (symm_map p)
  · exact D_J_maps_to_B_J p hp_prime
  · exact B_J_maps_to_D_J p hp_prime
  · intro u hu
    apply symm_map_symm_map
    exact mem_J_set_of_mem_D_J p u hu
  · intro u hu
    apply symm_map_symm_map
    exact mem_J_set_of_mem_B_J p u hu

theorem disjoint_D_J_B_J (p : ℕ) : Disjoint (D_J p) (B_J p) :=
by
  rw [Finset.disjoint_left]
  intro a ha ha'
  simp only [D_J, B_J, Finset.mem_filter] at ha ha'
  omega

theorem mem_D_J_iff_of_def (p u : ℕ) : u ∈ D_J p ↔ u ∈ J_set p ∧ (p : ℤ) + 3 ≤ (u : ℤ) + (modInv p u : ℤ) :=
by
  unfold D_J
  rw [Finset.mem_filter]

theorem mem_C_J_iff_of_def (p u : ℕ) : u ∈ C_J p ↔ u ∈ J_set p ∧ (p : ℤ) - 2 ≤ (u : ℤ) + (modInv p u : ℤ) ∧ (u : ℤ) + (modInv p u : ℤ) ≤ (p : ℤ) + 2 :=
by
  unfold C_J
  rw [Finset.mem_filter]

theorem disjoint_D_J_C_J (p : ℕ) : Disjoint (D_J p) (C_J p) :=
by
  rw [Finset.disjoint_left]
  intro u hu_D hu_C
  have hD := (mem_D_J_iff_of_def p u).mp hu_D
  have hC := (mem_C_J_iff_of_def p u).mp hu_C
  omega

theorem mem_B_J_iff_of_def (p u : ℕ) : u ∈ B_J p ↔ u ∈ J_set p ∧ (u : ℤ) + (modInv p u : ℤ) ≤ (p : ℤ) - 3 :=
by
  rw [B_J, Finset.mem_filter]

theorem disjoint_B_J_C_J (p : ℕ) : Disjoint (B_J p) (C_J p) :=
by
  rw [Finset.disjoint_left]
  intro u huB huC
  have hB := (mem_B_J_iff_of_def p u).mp huB
  have hC := (mem_C_J_iff_of_def p u).mp huC
  omega

theorem disjoint_D_J_union_B_J_C_J (p : ℕ) : Disjoint (D_J p ∪ B_J p) (C_J p) :=
by
  rw [Finset.disjoint_union_left]
  exact ⟨disjoint_D_J_C_J p, disjoint_B_J_C_J p⟩

theorem int_trichotomy_for_J_set (x p : ℤ) :
  p + 3 ≤ x ∨ x ≤ p - 3 ∨ (p - 2 ≤ x ∧ x ≤ p + 2) :=
by
  omega

theorem D_J_union_B_J_union_C_J_eq_J_set (p : ℕ) : D_J p ∪ B_J p ∪ C_J p = J_set p :=
by
  ext a
  -- We expand set unions and the membership rules into an equivalent logical statement.
  simp only [Finset.mem_union, mem_D_J_iff_of_def, mem_B_J_iff_of_def, mem_C_J_iff_of_def]
  -- Bring the fact that the combined condition is collectively exhaustive into the context.
  have h := int_trichotomy_for_J_set ((a : ℤ) + (modInv p a : ℤ)) (p : ℤ)
  -- The target reduces to verifying `(J ∧ P) ∨ (J ∧ Q) ∨ (J ∧ R) ↔ J` given `P ∨ Q ∨ R` is inherently True,
  -- which is a straightforward Propositional Logic tautology resolved beautifully by `tauto`.
  tauto

theorem J_set_partition (p : ℕ) (hp_prime : p.Prime) (hp : p ≥ 11) :
  (J_set p).card = (D_J p).card + (B_J p).card + (C_J p).card :=
by
  -- Substitute `J_set p` with its exact partitioned components.
  rw [← D_J_union_B_J_union_C_J_eq_J_set p]

  -- Since `∪` is left-associative, `D_J p ∪ B_J p ∪ C_J p` parses as `(D_J p ∪ B_J p) ∪ C_J p`.
  -- We first split off `C_J p` using our second disjointness lemma.
  rw [Finset.card_union_of_disjoint (disjoint_D_J_union_B_J_C_J p)]

  -- Finally, split the remaining union `(D_J p ∪ B_J p)` using our first disjointness lemma.
  rw [Finset.card_union_of_disjoint (disjoint_D_J_B_J p)]

theorem finset_card_le_two_of_forall_three_3 {α : Type*} (s : Finset α)
  (H : ∀ x ∈ s, ∀ y ∈ s, ∀ z ∈ s, x ≠ y → x ≠ z → y ≠ z → False) : s.card ≤ 2 :=
by
  by_contra h
  have h2 : 2 < s.card := by omega
  rw [Finset.two_lt_card_iff] at h2
  rcases h2 with ⟨x, y, z, hx, hy, hz, hxy, hxz, hyz⟩
  exact H x hx y hy z hz hxy hxz hyz

theorem quad_diff_factor {R : Type*} [CommRing R] (x y : R) :
  (x^2 + x + 1) - (y^2 + y + 1) = (x - y) * (x + y + 1) :=
by
  ring

theorem quad_roots_helper_1 (p : ℕ) [Fact p.Prime] (x y : ZMod p)
  (hx : x^2 + x + 1 = 0) (hy : y^2 + y + 1 = 0) (hxy : x ≠ y) : y = -x - 1 :=
by
  have h1 : (x - y) * (x + y + 1) = 0 := by
    calc (x - y) * (x + y + 1) = (x^2 + x + 1) - (y^2 + y + 1) := (quad_diff_factor x y).symm
      _ = 0 - 0 := by rw [hx, hy]
      _ = 0 := by ring
  cases mul_eq_zero.mp h1 with
  | inl h =>
    have h_eq : x = y := by
      calc x = (x - y) + y := by ring
           _ = 0 + y := by rw [h]
           _ = y := by ring
    exact absurd h_eq hxy
  | inr h =>
    calc y = (x + y + 1) - x - 1 := by ring
         _ = 0 - x - 1 := by rw [h]
         _ = -x - 1 := by ring

theorem quad_roots_bound_1 (p : ℕ) [Fact p.Prime] (s : Finset (ZMod p))
  (hs : ∀ x ∈ s, x^2 + x + 1 = 0) : s.card ≤ 2 :=
by
  apply finset_card_le_two_of_forall_three_3
  intro x hx y hy z hz hxy hxz hyz
  have h1 : y = -x - 1 := quad_roots_helper_1 p x y (hs x hx) (hs y hy) hxy
  have h2 : z = -x - 1 := quad_roots_helper_1 p x z (hs x hx) (hs z hz) hxz
  rw [h1, h2] at hyz
  exact hyz rfl

theorem quad_roots_eq_or_eq_neg (p : ℕ) [Fact p.Prime] (x y : ZMod p)
  (hx : x^2 + 1 = 0) (hy : y^2 + 1 = 0) : y = x ∨ y = -x :=
by
  -- Show that y^2 - x^2 = 0 algebraically
  have h1 : y^2 - x^2 = 0 := by
    calc
      y^2 - x^2 = (y^2 + 1) - (x^2 + 1) := by ring
      _ = 0 - (x^2 + 1) := by rw [hy]
      _ = 0 - 0 := by rw [hx]
      _ = 0 := by ring

  -- Rearrange to show that y^2 = x^2
  have h2 : y^2 = x^2 := by
    calc
      y^2 = (y^2 - x^2) + x^2 := by ring
      _ = 0 + x^2 := by rw [h1]
      _ = x^2 := by ring

  -- Apply the zero-divisor logic for equal squares
  exact sq_eq_sq_iff_eq_or_eq_neg.mp h2

theorem quad_roots_bound_2 (p : ℕ) [Fact p.Prime] (s : Finset (ZMod p))
  (hs : ∀ x ∈ s, x^2 + 1 = 0) : s.card ≤ 2 :=
by
  by_cases h : ∃ x, x ∈ s
  · rcases h with ⟨x, hx⟩
    have h_sub : s ⊆ insert x {-x} := by
      intro y hy
      have h1 := hs x hx
      have h2 := hs y hy
      have h3 := quad_roots_eq_or_eq_neg p x y h1 h2
      rw [Finset.mem_insert, Finset.mem_singleton]
      exact h3
    have h_card : (insert x {-x} : Finset (ZMod p)).card ≤ 2 := by
      have h1 := Finset.card_insert_le x ({-x} : Finset (ZMod p))
      have h2 : ({-x} : Finset (ZMod p)).card = 1 := Finset.card_singleton (-x)
      omega
    exact le_trans (Finset.card_le_card h_sub) h_card
  · push_neg at h
    have h_empty : s = ∅ := by
      ext a
      constructor
      · intro ha
        exact False.elim (h a ha)
      · intro ha
        simp_all
    rw [h_empty, Finset.card_empty]
    omega

theorem quad_roots_helper_3 (p : ℕ) [Fact p.Prime] (x y : ZMod p)
  (hx : x^2 - x + 1 = 0) (hy : y^2 - y + 1 = 0) (hxy : x ≠ y) : y = 1 - x :=
by
  -- Subtract the two equations and factor the result
  have h_mul : (y - x) * (y + x - 1) = 0 := by
    calc
      (y - x) * (y + x - 1) = (y^2 - y + 1) - (x^2 - x + 1) := by ring
      _ = 0 - (x^2 - x + 1) := by rw [hy]
      _ = 0 - 0 := by rw [hx]
      _ = 0 := by ring

  -- Since ZMod p is a field, the product is zero iff one of the factors is zero
  cases mul_eq_zero.mp h_mul with
  | inl h1 =>
    -- Case 1: y - x = 0
    have h_eq : x = y := by
      calc
        x = 0 + x := by ring
        _ = (y - x) + x := by rw [← h1]
        _ = y := by ring
    exfalso
    exact hxy h_eq

  | inr h2 =>
    -- Case 2: y + x - 1 = 0
    calc
      y = (y + x - 1) + 1 - x := by ring
      _ = 0 + 1 - x := by rw [h2]
      _ = 1 - x := by ring

theorem quad_roots_bound_3 (p : ℕ) [Fact p.Prime] (s : Finset (ZMod p))
  (hs : ∀ x ∈ s, x^2 - x + 1 = 0) : s.card ≤ 2 :=
by
  apply finset_card_le_two_of_forall_three_3
  intro x hx y hy z hz hxy hxz hyz
  have hy1 := quad_roots_helper_3 p x y (hs x hx) (hs y hy) hxy
  have hz1 := quad_roots_helper_3 p x z (hs x hx) (hs z hz) hxz
  rw [hy1, hz1] at hyz
  exact hyz rfl

theorem J_set_of_C_J (p u : ℕ) (hu : u ∈ C_J p) : u ∈ J_set p :=
by
  unfold C_J at hu
  exact (Finset.mem_filter.mp hu).1

theorem C_J_bounds_from_def (p u : ℕ) (hu : u ∈ C_J p) :
  (p : ℤ) - 2 ≤ (u : ℤ) + (modInv p u : ℤ) ∧ (u : ℤ) + (modInv p u : ℤ) ≤ (p : ℤ) + 2 :=
by
  unfold C_J at hu
  rw [Finset.mem_filter] at hu
  exact hu.2

theorem mem_C_J_eq_cases (p : ℕ) (u : ℕ) (hu : u ∈ C_J p) :
  (u : ℤ) + (modInv p u : ℤ) = (p : ℤ) - 2 ∨
  (u : ℤ) + (modInv p u : ℤ) = (p : ℤ) - 1 ∨
  (u : ℤ) + (modInv p u : ℤ) = (p : ℤ) ∨
  (u : ℤ) + (modInv p u : ℤ) = (p : ℤ) + 1 ∨
  (u : ℤ) + (modInv p u : ℤ) = (p : ℤ) + 2 :=
by
  have := C_J_bounds_from_def p u hu
  omega

theorem modInv_cast_ZMod (p : ℕ) [Fact p.Prime] (u : ℕ) :
  (modInv p u : ZMod p) = (u : ZMod p)⁻¹ :=
ZMod.natCast_zmod_val _

theorem cast_eq_neg_two (p : ℕ) [Fact p.Prime] (u : ℕ)
  (h : (u : ℤ) + (modInv p u : ℤ) = (p : ℤ) - 2) :
  (u : ZMod p) + (u : ZMod p)⁻¹ = -2 :=
by
  -- Apply the projection onto ZMod p to both sides of the integer equation
  have h1 := congr_arg (fun (x : ℤ) => (x : ZMod p)) h

  -- Push the integer casts inward so they simplify to natural number casts inside ZMod p
  push_cast at h1

  -- Rewrite the modInv projection to its multiplicative inverse equivalent
  rw [modInv_cast_ZMod] at h1

  -- Cast of the characteristic p is identically 0 in ZMod p
  have hp : (p : ZMod p) = 0 := CharP.cast_eq_zero (ZMod p) p
  rw [hp] at h1

  -- Verify the finalized simple arithmetic equality within ZMod p
  calc
    (u : ZMod p) + (u : ZMod p)⁻¹ = 0 - 2 := h1
    _ = -2 := by ring

theorem cast_eq_neg_one (p : ℕ) [Fact p.Prime] (u : ℕ)
  (h : (u : ℤ) + (modInv p u : ℤ) = (p : ℤ) - 1) :
  (u : ZMod p) + (u : ZMod p)⁻¹ = -1 :=
by
  -- Substitute the inverse representation in ZMod p
  rw [← modInv_cast_ZMod p u]

  -- Map the hypothesis `h` into `ZMod p`
  have h_cast := congrArg (fun x : ℤ ↦ (x : ZMod p)) h

  -- Push the integer casts down to the base elements (u, modInv p u, and p)
  push_cast at h_cast

  -- Rewrite the left hand side of the goal
  rw [h_cast]

  -- Use the characteristic identity for `ZMod p`
  have hp : (p : ZMod p) = 0 := CharP.cast_eq_zero (ZMod p) p
  rw [hp]

  -- Conclude the simple algebraic equality
  ring

theorem cast_eq_zero (p : ℕ) [Fact p.Prime] (u : ℕ)
  (h : (u : ℤ) + (modInv p u : ℤ) = (p : ℤ)) :
  (u : ZMod p) + (u : ZMod p)⁻¹ = 0 :=
by
  -- Apply the canonical cast from ℤ to ZMod p to both sides of hypothesis `h`
  have h1 := congrArg (fun x : ℤ => (x : ZMod p)) h

  -- Push the projection inside the addition on the left side
  -- and convert the base Nat casts correctly (`((p : ℤ) : ZMod p)` -> `(p : ZMod p)`)
  push_cast at h1

  -- Substitute the custom modulo inverse operation with the true field inversion in ZMod p
  rw [modInv_cast_ZMod] at h1

  -- Evaluate the equation and resolve the zero cast equality
  calc
    (u : ZMod p) + (u : ZMod p)⁻¹ = (p : ZMod p) := h1
    _ = 0 := by simp

theorem cast_eq_one (p : ℕ) [Fact p.Prime] (u : ℕ)
  (h : (u : ℤ) + (modInv p u : ℤ) = (p : ℤ) + 1) :
  (u : ZMod p) + (u : ZMod p)⁻¹ = 1 :=
by
  -- Apply the ring homomorphism from ℤ to ZMod p on both sides of our hypothesis
  have h1 := congrArg (fun x : ℤ => (x : ZMod p)) h

  -- Push the coercions to distribute the ZMod p cast over the additions
  push_cast at h1

  -- Substitute the casted modular inverse with the field inverse
  rw [modInv_cast_ZMod p u] at h1

  -- The characteristic of ZMod p ensures that (p : ZMod p) = 0
  have hp : (p : ZMod p) = 0 := CharP.cast_eq_zero (ZMod p) p

  -- Rewrite (p : ZMod p) to 0 and simplify 0 + 1 to 1
  rw [hp, zero_add] at h1

  -- The transformed equation perfectly matches the goal
  exact h1

theorem cast_eq_two (p : ℕ) [Fact p.Prime] (u : ℕ)
  (h : (u : ℤ) + (modInv p u : ℤ) = (p : ℤ) + 2) :
  (u : ZMod p) + (u : ZMod p)⁻¹ = 2 :=
by
  -- Apply the canonical cast from ℤ to ZMod p to the equality
  have h1 := congrArg (fun x : ℤ => (x : ZMod p)) h

  -- Distribute the cast over addition
  push_cast at h1

  -- Rewrite the casted inverse using the provided lemma
  rw [modInv_cast_ZMod p u] at h1

  -- In ZMod p, the element corresponding to p is 0
  have hp : (p : ZMod p) = 0 := ZMod.natCast_self p

  -- Substitute p with 0 and simplify the addition
  rw [hp, zero_add] at h1

  -- h1 now perfectly matches our goal
  exact h1

theorem cast_mem_C_J_cases (p : ℕ) [Fact p.Prime] (u : ℕ)
  (h : (u : ℤ) + (modInv p u : ℤ) = (p : ℤ) - 2 ∨
       (u : ℤ) + (modInv p u : ℤ) = (p : ℤ) - 1 ∨
       (u : ℤ) + (modInv p u : ℤ) = (p : ℤ) ∨
       (u : ℤ) + (modInv p u : ℤ) = (p : ℤ) + 1 ∨
       (u : ℤ) + (modInv p u : ℤ) = (p : ℤ) + 2) :
  (u : ZMod p) + (u : ZMod p)⁻¹ = -2 ∨
  (u : ZMod p) + (u : ZMod p)⁻¹ = -1 ∨
  (u : ZMod p) + (u : ZMod p)⁻¹ = 0 ∨
  (u : ZMod p) + (u : ZMod p)⁻¹ = 1 ∨
  (u : ZMod p) + (u : ZMod p)⁻¹ = 2 :=
by
  rcases h with h1 | h2 | h3 | h4 | h5
  · exact Or.inl (cast_eq_neg_two p u h1)
  · exact Or.inr (Or.inl (cast_eq_neg_one p u h2))
  · exact Or.inr (Or.inr (Or.inl (cast_eq_zero p u h3)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (cast_eq_one p u h4))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (cast_eq_two p u h5))))

theorem mem_J_set_bounds (p u : ℕ) (hu : u ∈ J_set p) : 2 ≤ u ∧ u + 2 ≤ p :=
by
  simp_all [J_set, Finset.mem_Icc, Finset.mem_Ico, Set.mem_Icc, Set.mem_Ico, Set.mem_setOf_eq]
  omega

theorem J_set_ZMod_not_zero (p : ℕ) [Fact p.Prime] (hp : p ≥ 11) (u : ℕ) (hu : u ∈ J_set p) :
  (u : ZMod p) ≠ 0 :=
by
  intro h
  have h_bounds : 2 ≤ u ∧ u + 2 ≤ p := mem_J_set_bounds p u hu
  have h_lt : u < p := by omega
  have h_val : (u : ZMod p).val = u := ZMod.val_cast_of_lt h_lt
  have h_zero : (0 : ZMod p).val = 0 := ZMod.val_zero
  rw [h] at h_val
  rw [h_zero] at h_val
  omega

theorem J_set_ge_two (p u : ℕ) (hu : u ∈ J_set p) : 2 ≤ u :=
(Finset.mem_Icc.mp hu).1

theorem u_lt_p_of_mem_J_set (p u : ℕ) (hu : u ∈ J_set p) : u < p :=
by
  have h := (mem_J_set_bounds p u hu).2
  omega

theorem J_set_ZMod_val_u (p u : ℕ) [Fact p.Prime] (hp : p ≥ 11) (hu : u ∈ J_set p) :
  (u : ZMod p).val = u :=
by
  have h_lt : u < p := u_lt_p_of_mem_J_set p u hu
  exact ZMod.val_natCast_of_lt h_lt

theorem p_ne_one_of_ge_11 (p : ℕ) (hp : p ≥ 11) : p ≠ 1 :=
by
  omega

theorem ZMod_val_one_of_ge_11 (p : ℕ) [Fact p.Prime] (hp : p ≥ 11) :
  (1 : ZMod p).val = 1 :=
by
  apply ZMod.val_one''
  exact p_ne_one_of_ge_11 p hp

theorem J_set_ZMod_not_one (p : ℕ) [Fact p.Prime] (hp : p ≥ 11) (u : ℕ) (hu : u ∈ J_set p) :
  (u : ZMod p) ≠ 1 :=
by
  intro h
  have h1 : u = 1 := by
    calc
      u = (u : ZMod p).val := (J_set_ZMod_val_u p u hp hu).symm
      _ = (1 : ZMod p).val := by rw [h]
      _ = 1                := ZMod_val_one_of_ge_11 p hp
  have h2 : 2 ≤ u := J_set_ge_two p u hu
  omega

theorem dvd_add_one_of_eq_neg_one (p u : ℕ) [Fact p.Prime] (h : (u : ZMod p) = -1) :
  p ∣ u + 1 :=
by
  have h1 : ((u + 1 : ℕ) : ZMod p) = 0 := by
    push_cast
    rw [h]
    ring
  exact (CharP.cast_eq_zero_iff (ZMod p) p (u + 1)).mp h1

theorem mem_J_set_add_one_pos (p u : ℕ) (hu : u ∈ J_set p) : 0 < u + 1 :=
by
  omega

theorem mem_J_set_add_one_lt_p (p u : ℕ) (hu : u ∈ J_set p) : u + 1 < p :=
by
  have h := mem_J_set_bounds p u hu
  omega

theorem not_dvd_add_one_of_mem_J_set (p u : ℕ) (hu : u ∈ J_set p) :
  ¬ (p ∣ u + 1) :=
by
  intro h
  have h_pos := mem_J_set_add_one_pos p u hu
  have h_lt := mem_J_set_add_one_lt_p p u hu
  have h_le := Nat.le_of_dvd h_pos h
  omega

theorem J_set_ZMod_not_neg_one (p : ℕ) [Fact p.Prime] (hp : p ≥ 11) (u : ℕ) (hu : u ∈ J_set p) :
  (u : ZMod p) ≠ -1 :=
by
  intro h
  have h1 : p ∣ u + 1 := dvd_add_one_of_eq_neg_one p u h
  have h2 : ¬(p ∣ u + 1) := not_dvd_add_one_of_mem_J_set p u hu
  exact h2 h1

theorem CJ_poly_case_neg2_helper (p : ℕ) [Fact p.Prime] (x : ZMod p) (hx0 : x ≠ 0) (h : x + x⁻¹ = -2) :
  (x + 1)^2 = 0 :=
by
  -- Obtain the inverse property from the field structure of ZMod p (since p is prime and x ≠ 0)
  have h_inv : x * x⁻¹ = 1 := mul_inv_cancel₀ hx0

  -- Use a series of algebraic steps to demonstrate the equality
  calc
    (x + 1)^2 = x * ((x + x⁻¹) + 2) - x * x⁻¹ + 1 := by ring
    _ = x * (-2 + 2) - x * x⁻¹ + 1                := by rw [h]
    _ = x * (-2 + 2) - 1 + 1                      := by rw [h_inv]
    _ = 0                                         := by ring

theorem CJ_poly_case_neg2 (p : ℕ) [Fact p.Prime] (x : ZMod p) (hx0 : x ≠ 0) (h : x + x⁻¹ = -2) :
  x = -1 :=
by
  -- Utilize our structured helper lemma
  have h_sq : (x + 1)^2 = 0 := CJ_poly_case_neg2_helper p x hx0 h

  -- Expand the perfect square back to standard factorization formats
  have h_mul : (x + 1) * (x + 1) = 0 := by
    calc (x + 1) * (x + 1) = (x + 1)^2 := by ring
    _ = 0 := h_sq

  -- Since ZMod p is an integral domain (as p is prime), (x + 1) * (x + 1) = 0 implies x + 1 = 0
  have h_add : x + 1 = 0 := by
    cases mul_eq_zero.mp h_mul with
    | inl h1 => exact h1
    | inr h2 => exact h2

  -- Finally, rearranging x + 1 = 0 easily gives x = -1
  -- We use strictly addition to avoid any parsing/typing ambiguity with subtraction
  calc x = x + 1 + -1 := by ring
    _ = 0 + -1 := by rw [h_add]
    _ = -1 := by ring

theorem CJ_poly_case_neg1 (p : ℕ) [Fact p.Prime] (x : ZMod p) (hx0 : x ≠ 0) (h : x + x⁻¹ = -1) :
  x^2 + x + 1 = 0 :=
by
  have h1 : x * x⁻¹ = 1 := mul_inv_cancel₀ hx0
  calc
    x^2 + x + 1 = x * (x + x⁻¹) + x + 1 - x * x⁻¹ := by ring
    _ = x * (-1) + x + 1 - 1 := by rw [h, h1]
    _ = 0 := by ring

theorem CJ_poly_case_zero (p : ℕ) [Fact p.Prime] (x : ZMod p) (hx0 : x ≠ 0) (h : x + x⁻¹ = 0) :
  x^2 + 1 = 0 :=
by
  rw [sq, ← mul_inv_cancel₀ hx0, ← mul_add, h, mul_zero]

theorem CJ_poly_case_one (p : ℕ) [Fact p.Prime] (x : ZMod p) (hx0 : x ≠ 0) (h : x + x⁻¹ = 1) :
  x^2 - x + 1 = 0 :=
by
  have h2 : x⁻¹ * x = 1 := inv_mul_cancel₀ hx0
  calc
    x^2 - x + 1 = x^2 - x + x⁻¹ * x := by rw [h2]
    _ = (x + x⁻¹) * x - x := by ring
    _ = 1 * x - x := by rw [h]
    _ = 0 := by ring

theorem CJ_poly_case_two_helper (p : ℕ) [Fact p.Prime] (x : ZMod p) (hx0 : x ≠ 0) (h : x + x⁻¹ = 2) :
  (x - 1) * (x - 1) = 0 :=
by
  -- Since p is prime, ZMod p is a field and x * x⁻¹ = 1 for any non-zero x.
  -- We use a fallback to support different versions of Mathlib 4 naming.
  have h1 : x * x⁻¹ = 1 := by
    first
    | exact mul_inv_cancel₀ hx0
    | exact mul_inv_cancel hx0

  -- Use direct equational rewrites and ring automation
  calc
    (x - 1) * (x - 1) = x * (x + x⁻¹) - 2 * x + 1 - x * x⁻¹ := by ring
    _                 = x * 2 - 2 * x + 1 - 1               := by rw [h, h1]
    _                 = 0                                   := by ring

theorem CJ_poly_case_two (p : ℕ) [Fact p.Prime] (x : ZMod p) (hx0 : x ≠ 0) (h : x + x⁻¹ = 2) :
  x = 1 :=
by
  have h_mul : (x - 1) * (x - 1) = 0 := CJ_poly_case_two_helper p x hx0 h
  have h_zero : x - 1 = 0 := mul_self_eq_zero.mp h_mul
  calc
    x = (x - 1) + 1 := by ring
    _ = 0 + 1 := by rw [h_zero]
    _ = 1 := by ring

theorem CJ_poly_cases_helper (p : ℕ) [Fact p.Prime] (x : ZMod p) (hx1 : x ≠ 1) (hxm1 : x ≠ -1) (hx0 : x ≠ 0)
  (h : x + x⁻¹ = -2 ∨ x + x⁻¹ = -1 ∨ x + x⁻¹ = 0 ∨ x + x⁻¹ = 1 ∨ x + x⁻¹ = 2) :
  x^2 + x + 1 = 0 ∨ x^2 + 1 = 0 ∨ x^2 - x + 1 = 0 :=
by
  rcases h with h_neg2 | h_neg1 | h_zero | h_one | h_two
  · exact False.elim (hxm1 (CJ_poly_case_neg2 p x hx0 h_neg2))
  · exact Or.inl (CJ_poly_case_neg1 p x hx0 h_neg1)
  · exact Or.inr (Or.inl (CJ_poly_case_zero p x hx0 h_zero))
  · exact Or.inr (Or.inr (CJ_poly_case_one p x hx0 h_one))
  · exact False.elim (hx1 (CJ_poly_case_two p x hx0 h_two))

theorem CJ_poly_cases (p : ℕ) [Fact p.Prime] (hp : p ≥ 11) (u : ℕ) (hu : u ∈ C_J p) :
  ((u : ZMod p)^2 + (u : ZMod p) + 1 = 0) ∨ ((u : ZMod p)^2 + 1 = 0) ∨ ((u : ZMod p)^2 - (u : ZMod p) + 1 = 0) :=
by
  have hu_J := J_set_of_C_J p u hu
  have h_not_zero := J_set_ZMod_not_zero p hp u hu_J
  have h_not_one := J_set_ZMod_not_one p hp u hu_J
  have h_not_neg_one := J_set_ZMod_not_neg_one p hp u hu_J
  have h_cases := mem_C_J_eq_cases p u hu
  have h_cast := cast_mem_C_J_cases p u h_cases
  exact CJ_poly_cases_helper p (u : ZMod p) h_not_one h_not_neg_one h_not_zero h_cast

theorem mem_J_set_lt_p (p u : ℕ) (hp : p ≥ 11) (hu : u ∈ J_set p) : u < p :=
by
  simp_all [J_set]
  omega

theorem C_J_image_inj (p : ℕ) [Fact p.Prime] (hp : p ≥ 11) {u v : ℕ} (hu : u ∈ C_J p) (hv : v ∈ C_J p)
  (h : (u : ZMod p) = (v : ZMod p)) : u = v :=
by
  have hu_J : u ∈ J_set p := J_set_of_C_J p u hu
  have hv_J : v ∈ J_set p := J_set_of_C_J p v hv
  have hu_lt : u < p := mem_J_set_lt_p p u hp hu_J
  have hv_lt : v < p := mem_J_set_lt_p p v hp hv_J
  have h_mod : u % p = v % p := by
    rw [ZMod.natCast_eq_natCast_iff'] at h
    exact h
  rw [Nat.mod_eq_of_lt hu_lt, Nat.mod_eq_of_lt hv_lt] at h_mod
  exact h_mod

theorem C_J_bound (p : ℕ) (hp_prime : p.Prime) (hp : p ≥ 11) :
  (C_J p).card ≤ 6 :=
by
  haveI : Fact p.Prime := ⟨hp_prime⟩
  let S := (C_J p).image (fun u : ℕ => (u : ZMod p))

  -- The cardinality is preserved under the injective map over C_J p
  have hS_card : S.card = (C_J p).card := by
    apply Finset.card_image_of_injOn
    intro u hu v hv huv
    exact C_J_image_inj p hp hu hv huv
  rw [← hS_card]

  -- Define subsets based on the three mutually exclusive quadratic conditions
  let S1 := S.filter (fun x => x^2 + x + 1 = 0)
  let S2 := S.filter (fun x => x^2 + 1 = 0)
  let S3 := S.filter (fun x => x^2 - x + 1 = 0)

  have hS_sub : S ⊆ S1 ∪ S2 ∪ S3 := by
    intro x hx
    rcases Finset.mem_image.1 hx with ⟨u, hu, rfl⟩
    have h_cases := CJ_poly_cases p hp u hu
    rcases h_cases with h1 | h2 | h3
    · apply Finset.mem_union.2
      left
      apply Finset.mem_union.2
      left
      exact Finset.mem_filter.2 ⟨hx, h1⟩
    · apply Finset.mem_union.2
      left
      apply Finset.mem_union.2
      right
      exact Finset.mem_filter.2 ⟨hx, h2⟩
    · apply Finset.mem_union.2
      right
      exact Finset.mem_filter.2 ⟨hx, h3⟩

  -- Compile bounds
  have h_card_sub : S.card ≤ (S1 ∪ S2 ∪ S3).card := Finset.card_le_card hS_sub
  have h_union1 : (S1 ∪ S2 ∪ S3).card ≤ (S1 ∪ S2).card + S3.card := Finset.card_union_le (S1 ∪ S2) S3
  have h_union2 : (S1 ∪ S2).card ≤ S1.card + S2.card := Finset.card_union_le S1 S2

  -- Apply quadratic bounds
  have h_S1 : S1.card ≤ 2 := quad_roots_bound_1 p S1 (fun x hx => (Finset.mem_filter.1 hx).2)
  have h_S2 : S2.card ≤ 2 := quad_roots_bound_2 p S2 (fun x hx => (Finset.mem_filter.1 hx).2)
  have h_S3 : S3.card ≤ 2 := quad_roots_bound_3 p S3 (fun x hx => (Finset.mem_filter.1 hx).2)

  -- Conclude sum restriction
  omega

theorem J_set_card (p : ℕ) (hp : p ≥ 11) : (J_set p).card = p - 3 :=
by
  unfold J_set
  rw [Nat.card_Icc]
  omega

theorem D_lower_bound (p : ℕ) (hp_prime : p.Prime) : p ≤ 2 * descentCount p + 7 :=
by
  by_cases hp11 : p < 11
  · have hp7 : p ≤ 7 := by
      by_contra! h
      -- Narrowing down specific non-primes between 7 < p < 11 to deduce bounds
      interval_cases p
      · revert hp_prime; decide
      · revert hp_prime; decide
      · revert hp_prime; decide
    omega
  · have hp11_ge : p ≥ 11 := by omega
    have h1 : descentCount p = (D_J p).card + 1 := by
      rw [descent_count_eq_u_set p hp_prime]
      rw [u_set_eq_D_J_plus_one p hp_prime hp11_ge]
    have h2 : (J_set p).card = (D_J p).card + (B_J p).card + (C_J p).card :=
      J_set_partition p hp_prime hp11_ge
    have h3 : (D_J p).card = (B_J p).card :=
      D_J_B_J_symm p hp_prime
    have h4 : (J_set p).card = p - 3 :=
      J_set_card p hp11_ge
    have h5 : (C_J p).card ≤ 6 :=
      C_J_bound p hp_prime hp11_ge
    omega

theorem prime_cases (p : ℕ) (hp_prime : p.Prime) (hp3 : 3 < p) (hp11 : p < 11) : p = 5 ∨ p = 7 :=
by
  revert hp_prime
  interval_cases p <;> decide

theorem putnam_2025_b5 (p : ℕ)
    (hp_prime : p.Prime)
    (hp_gt : 3 < p) : (p : ℚ) / 4 - 1 < descentCount p :=
by
  have h_bound := D_lower_bound p hp_prime
  by_cases hp11 : p < 11
  · have h57 := prime_cases p hp_prime hp_gt hp11
    rcases h57 with rfl | rfl
    · rw [descent_count_5]
      norm_num
    · rw [descent_count_7]
      norm_num
  · push_neg at hp11
    have h1 : (p : ℚ) ≤ 2 * (descentCount p : ℚ) + 7 := by exact_mod_cast h_bound
    have h2 : (11 : ℚ) ≤ (p : ℚ) := by exact_mod_cast hp11
    linarith
