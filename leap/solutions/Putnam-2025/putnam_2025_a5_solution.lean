import Mathlib
open Finset
abbrev putnam_2025_a5_solution : (n : ℕ) → Set (Fin n → ℤˣ) :=
  fun n => {s | ∀ (i : Fin n), (h : i.val + 1 < n) → s ⟨i.val + 1, h⟩ = -s i}
abbrev f (n : ℕ) (s : Fin n → ℤˣ) : ℕ :=
  Finset.card {σ : Equiv.Perm (Fin (n + 1)) |
    ∀ i : Fin n, 0 < (s i : ℤ) * ((σ i.succ : ℤ) - (σ i.castSucc : ℤ))}

def I (n : ℕ) (A : Fin (n + 1) → ℕ) : Fin (n + 2) → ℕ :=
  fun k => ∑ i : Fin (n + 1), if i.val < k.val then A i else 0
def J (n : ℕ) (A : Fin (n + 1) → ℕ) : Fin (n + 2) → ℕ :=
  fun k => ∑ i : Fin (n + 1), if k.val ≤ i.val then A i else 0
def V : ∀ n, (Fin n → ℤˣ) → Fin (n + 1) → ℕ
| 0, _ => fun _ => 1
| n + 1, s =>
  let s_prev := fun i : Fin n => s (Fin.castSucc i)
  if s (Fin.last n) = (1 : ℤˣ) then
    I n (V n s_prev)
  else
    J n (V n s_prev)
mutual
def V_alt1 : ∀ n, Fin (n + 1) → ℕ
| 0 => fun _ => 1
| n + 1 => I n (V_alt2 n)
def V_alt2 : ∀ n, Fin (n + 1) → ℕ
| 0 => fun _ => 1
| n + 1 => J n (V_alt1 n)
end
def SumA (n : ℕ) (A : Fin (n + 1) → ℕ) : ℕ := ∑ k, A k
mutual
def alt1_seq : ∀ n, Fin n → ℤˣ
| 0 => Fin.elim0
| n + 1 => Fin.snoc (alt2_seq n) (1 : ℤˣ)
def alt2_seq : ∀ n, Fin n → ℤˣ
| 0 => Fin.elim0
| n + 1 => Fin.snoc (alt1_seq n) (-1 : ℤˣ)
end
def ValidPermsEnd (n : ℕ) (s : Fin n → ℤˣ) (k : Fin (n + 1)) : Finset (Equiv.Perm (Fin (n + 1))) :=
  Finset.filter (fun σ => σ (Fin.last n) = k ∧
    ∀ i : Fin n, 0 < (s i : ℤ) * ((σ i.succ : ℤ) - (σ i.castSucc : ℤ))) Finset.univ

def extendFun {n : ℕ} (k : Fin (n+2)) (τ : Equiv.Perm (Fin (n+1))) : Fin (n+2) → Fin (n+2) :=
  Fin.lastCases k (fun i => Fin.succAbove k (τ i))
noncomputable def extendPerm {n : ℕ} (k : Fin (n+2)) (τ : Equiv.Perm (Fin (n+1))) : Equiv.Perm (Fin (n+2)) :=
  @Classical.epsilon (Equiv.Perm (Fin (n+2))) (Nonempty.intro (Equiv.refl (Fin (n+2)))) (fun σ => ∀ i, σ i = extendFun k τ i)

def d_coeff (k s : ℤ) : ℤ := max (0 : ℤ) (s + (1 : ℤ) - k)
def c_coeff_pre (d k m : ℤ) : ℤ := max (0 : ℤ) (d + (2 : ℤ) - max k (m + (1 : ℤ)))
def c_coeff (d k s : ℤ) : ℤ := max (0 : ℤ) (d + (2 : ℤ) - max k (d - s + (1 : ℤ)))

def I_coeff (d : ℕ) (i : Fin (d + 1)) : ℕ :=
  Finset.sum Finset.univ (fun (k : Fin (d + 2)) => if (i : ℕ) < (k : ℕ) then 1 else 0)

def F2_to_F1_fun (n : ℕ) (k : Fin (n + 2)) (x : Fin (n + 1)) : Fin (n + 1) :=
  if h : (x : ℕ) + (k : ℕ) < n + 1 then
    ⟨(x : ℕ) + (k : ℕ), h⟩
  else
    ⟨0, by omega⟩

theorem I_V_alt2_eq (d : ℕ) (k : Fin (d + 2)) : I d (V_alt2 d) k = V_alt1 (d + 1) k :=
by
  rfl

theorem J_V_alt1_eq (d : ℕ) (k : Fin (d + 2)) : J d (V_alt1 d) k = V_alt2 (d + 1) k :=
rfl

theorem V_alt2_eq_rev_base (k : Fin 1) :
  V_alt2 0 k = V_alt1 0 (k.rev) :=
rfl

theorem fin_rev_rev (n : ℕ) (i : Fin (n + 1)) :
  i.rev.rev = i :=
by
  ext
  simp only [Fin.rev]
  omega

theorem J_eq_sum_filter (n : ℕ) (A : Fin (n + 1) → ℕ) (k : Fin (n + 2)) :
  J n A k = Finset.sum (Finset.filter (fun j : Fin (n + 1) => (k : ℕ) ≤ (j : ℕ)) Finset.univ) A :=
by
  symm
  rw [Finset.sum_filter]
  rfl

theorem I_eq_sum_filter (n : ℕ) (A : Fin (n + 1) → ℕ) (k : Fin (n + 2)) :
  I n A k = Finset.sum (Finset.filter (fun j : Fin (n + 1) => (j : ℕ) < (k : ℕ)) Finset.univ) A :=
by
  rw [Finset.sum_filter]
  rfl

theorem rev_condition_fwd (n : ℕ) (k : Fin (n + 2)) (j : Fin (n + 1)) (hj : (k : ℕ) ≤ (j : ℕ)) :
  (j.rev : ℕ) < (k.rev : ℕ) :=
by
  have h1 : (j : ℕ) < n + 1 := j.isLt
  have h2 : (k : ℕ) < n + 2 := k.isLt
  unfold Fin.rev
  dsimp only
  omega

theorem rev_condition_bwd (n : ℕ) (k : Fin (n + 2)) (j : Fin (n + 1)) (hj : (j : ℕ) < (k.rev : ℕ)) :
  (k : ℕ) ≤ (j.rev : ℕ) :=
by
  simp only [Fin.val_rev] at hj ⊢
  omega

theorem fin_rev_rev_eq {n : ℕ} (k : Fin (n + 1)) : k.rev.rev = k :=
by
  exact Fin.rev_involutive k

theorem sum_filter_eq_sum_filter_rev (n : ℕ) (A B : Fin (n + 1) → ℕ) (h : ∀ j, A j = B (j.rev)) (k : Fin (n + 2)) :
  Finset.sum (Finset.filter (fun j : Fin (n + 1) => (k : ℕ) ≤ (j : ℕ)) Finset.univ) A =
  Finset.sum (Finset.filter (fun j : Fin (n + 1) => (j : ℕ) < (k.rev : ℕ)) Finset.univ) B :=
by
  refine Finset.sum_bij (fun (j : Fin (n + 1)) _ => j.rev) ?_ ?_ ?_ ?_
  · intro j hj
    rw [Finset.mem_filter] at hj ⊢
    exact ⟨Finset.mem_univ j.rev, rev_condition_fwd n k j hj.2⟩
  · intro a ha b hb hab
    change a.rev = b.rev at hab
    calc a = a.rev.rev := (fin_rev_rev_eq a).symm
         _ = b.rev.rev := by rw [hab]
         _ = b         := fin_rev_rev_eq b
  · intro b hb
    have hb' := hb
    rw [Finset.mem_filter] at hb'
    have ha : b.rev ∈ Finset.filter (fun j : Fin (n + 1) => (k : ℕ) ≤ (j : ℕ)) Finset.univ := by
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ b.rev, rev_condition_bwd n k b hb'.2⟩
    exact ⟨b.rev, ha, fin_rev_rev_eq b⟩
  · intro j hj
    exact h j

theorem J_eq_I_rev (n : ℕ) (A B : Fin (n + 1) → ℕ) (h : ∀ j, A j = B (j.rev)) (k : Fin (n + 2)) :
  J n A k = I n B (k.rev) :=
by
  rw [J_eq_sum_filter, I_eq_sum_filter]
  exact sum_filter_eq_sum_filter_rev n A B h k

theorem V_alt2_eq_rev (n : ℕ) (k : Fin (n + 1)) :
  V_alt2 n k = V_alt1 n (k.rev) :=
by
  revert k
  induction n with
  | zero =>
    intro k
    exact V_alt2_eq_rev_base k
  | succ n ih =>
    intro k
    rw [← J_V_alt1_eq n k, ← I_V_alt2_eq n (k.rev)]
    apply J_eq_I_rev
    intro j
    have h1 := ih (j.rev)
    rw [fin_rev_rev n j] at h1
    exact h1.symm

theorem SumA_eq_sum (n : ℕ) (A : Fin (n + 1) → ℕ) : SumA n A = Finset.sum Finset.univ A :=
rfl

theorem SumA_rev_eq (n : ℕ) (A : Fin (n + 1) → ℕ) :
  SumA n (fun k => A k.rev) = SumA n A :=
by
  rw [SumA_eq_sum, SumA_eq_sum]
  let finRevEquiv : Fin (n + 1) ≃ Fin (n + 1) := {
    toFun := Fin.rev
    invFun := Fin.rev
    left_inv := fun k => fin_rev_rev_eq k
    right_inv := fun k => fin_rev_rev_eq k
  }
  exact Equiv.sum_comp finRevEquiv A

theorem SumA_V_alt1_eq_SumA_V_alt2 (n : ℕ) : SumA n (V_alt1 n) = SumA n (V_alt2 n) :=
by
  -- Establish functional equality between V_alt2 n and the reversed V_alt1 n
  have h1 : V_alt2 n = fun k => V_alt1 n k.rev := by
    funext k
    exact V_alt2_eq_rev n k

  -- Apply congrArg to substitute the function directly into SumA
  have h2 : SumA n (V_alt2 n) = SumA n (fun k => V_alt1 n k.rev) := by
    exact congrArg (SumA n) h1

  -- Rewrite the main goal and conclude using our reversed summation lemma
  rw [h2]
  exact (SumA_rev_eq n (V_alt1 n)).symm

theorem sol_zero (s : Fin 0 → ℤˣ) : s ∈ putnam_2025_a5_solution 0 :=
by
  intro i
  exact Fin.elim0 i

theorem alt1_seq_castSucc (n : ℕ) : (fun i : Fin n => alt1_seq (n + 1) (Fin.castSucc i)) = alt2_seq n :=
by
  change Fin.snoc (alt2_seq n) (1 : ℤˣ) ∘ Fin.castSucc = alt2_seq n
  exact Fin.snoc_comp_castSucc

theorem alt1_seq_last (n : ℕ) : alt1_seq (n + 1) (Fin.last n) = (1 : ℤˣ) :=
by
  simp [alt1_seq, Fin.snoc_last]

theorem alt2_seq_last (n : ℕ) : alt2_seq (n + 1) (Fin.last n) = (-1 : ℤˣ) :=
by
  simp [alt2_seq, Fin.snoc_last]

theorem units_neg_neg_one : -(-1 : ℤˣ) = (1 : ℤˣ) :=
neg_neg (1 : ℤˣ)

theorem alt1_seq_castSucc_eval (n : ℕ) (i : Fin n) :
  alt1_seq (n + 1) (Fin.castSucc i) = alt2_seq n i :=
congrFun (Fin.snoc_comp_castSucc (f := alt2_seq n) (a := (1 : ℤˣ))) i

theorem alt1_seq_in_sol_step (n : ℕ) (ih : alt2_seq n ∈ putnam_2025_a5_solution n) :
  alt1_seq (n + 1) ∈ putnam_2025_a5_solution (n + 1) :=
by
  intro i h
  -- Using `i.val` explicitly instead of destructuring via `obtain` prevents type mismatch problems during `omega`.
  cases n with
  | zero =>
    -- Base case: n = 0, no adjacent elements exist.
    omega
  | succ m =>
    -- Step case: Evaluate the index position and check if it crosses the boundary of the appended element.
    by_cases heq : i.val + 1 = m + 1
    · -- Boundary case: `i.val + 1 = m + 1`. We reach the end index.
      have h_i : i.val = m := by omega

      have eq1 : (⟨i.val + 1, h⟩ : Fin (m + 2)) = Fin.last (m + 1) := by
        apply Fin.ext
        exact heq

      have eq2 : i = Fin.castSucc (Fin.last m) := by
        apply Fin.ext
        exact h_i

      -- Rewrite exactly the isolated constructors cleanly
      rw [eq1, eq2]
      rw [alt1_seq_last, alt1_seq_castSucc_eval, alt2_seq_last]
      exact units_neg_neg_one.symm

    · -- Bulk case: The indices firmly fall strictly into the previously generated sequence part.
      have hlt : i.val + 1 < m + 1 := by omega
      have hj : i.val < m + 1 := by omega

      let j : Fin (m + 1) := ⟨i.val, hj⟩
      let k : Fin (m + 1) := ⟨i.val + 1, hlt⟩

      have eq1 : (⟨i.val + 1, h⟩ : Fin (m + 2)) = Fin.castSucc k := by
        apply Fin.ext
        rfl

      have eq2 : i = Fin.castSucc j := by
        apply Fin.ext
        rfl

      -- Rewrite the evaluations locally to apply the induction hypothesis effortlessly
      rw [eq1, eq2]
      rw [alt1_seq_castSucc_eval, alt1_seq_castSucc_eval]

      exact ih j hlt

theorem alt2_seq_castSucc (n : ℕ) : (fun i : Fin n => alt2_seq (n + 1) (Fin.castSucc i)) = alt1_seq n :=
by
  ext i
  -- Unfolds the `n + 1` definition of `alt2_seq` which translates to `Fin.snoc`,
  -- and automatically uses `Fin.snoc_castSucc` to eliminate the cast point-wise.
  simp [alt2_seq, Fin.snoc_castSucc]

theorem units_neg_one : -(1 : ℤˣ) = (-1 : ℤˣ) :=
rfl

theorem alt2_seq_in_sol_step (n : ℕ) (ih : alt1_seq n ∈ putnam_2025_a5_solution n) :
  alt2_seq (n + 1) ∈ putnam_2025_a5_solution (n + 1) :=
by
  cases n with
  | zero =>
    intro i h
    exfalso
    omega
  | succ m =>
    intro i h
    have h_lt : i.val < m + 1 := by omega

    have eq1 : alt2_seq (m + 2) i = alt1_seq (m + 1) ⟨i.val, h_lt⟩ := by
      have h_cast : i = Fin.castSucc ⟨i.val, h_lt⟩ := Fin.ext rfl
      have step1 : alt2_seq (m + 2) i = alt2_seq (m + 2) (Fin.castSucc ⟨i.val, h_lt⟩) :=
        congrArg (alt2_seq (m + 2)) h_cast
      have step2 : alt2_seq (m + 2) (Fin.castSucc ⟨i.val, h_lt⟩) = alt1_seq (m + 1) ⟨i.val, h_lt⟩ :=
        congr_fun (alt2_seq_castSucc (m + 1)) ⟨i.val, h_lt⟩
      exact step1.trans step2

    by_cases h2 : i.val + 1 < m + 1
    · have eq2 : alt2_seq (m + 2) ⟨i.val + 1, h⟩ = alt1_seq (m + 1) ⟨i.val + 1, h2⟩ := by
        have h_cast2 : (⟨i.val + 1, h⟩ : Fin (m + 2)) = Fin.castSucc ⟨i.val + 1, h2⟩ := Fin.ext rfl
        have step1 : alt2_seq (m + 2) ⟨i.val + 1, h⟩ = alt2_seq (m + 2) (Fin.castSucc ⟨i.val + 1, h2⟩) :=
          congrArg (alt2_seq (m + 2)) h_cast2
        have step2 : alt2_seq (m + 2) (Fin.castSucc ⟨i.val + 1, h2⟩) = alt1_seq (m + 1) ⟨i.val + 1, h2⟩ :=
          congr_fun (alt2_seq_castSucc (m + 1)) ⟨i.val + 1, h2⟩
        exact step1.trans step2
      rw [eq1, eq2]
      exact ih ⟨i.val, h_lt⟩ h2

    · have eq_LHS : alt2_seq (m + 2) ⟨i.val + 1, h⟩ = (-1 : ℤˣ) := by
        have h_last1 : (⟨i.val + 1, h⟩ : Fin (m + 2)) = Fin.last (m + 1) := by
          apply Fin.ext
          change i.val + 1 = m + 1
          omega
        have step1 : alt2_seq (m + 2) ⟨i.val + 1, h⟩ = alt2_seq (m + 2) (Fin.last (m + 1)) :=
          congrArg (alt2_seq (m + 2)) h_last1
        have step2 : alt2_seq (m + 2) (Fin.last (m + 1)) = (-1 : ℤˣ) := alt2_seq_last (m + 1)
        exact step1.trans step2

      have eq_RHS : -alt1_seq (m + 1) ⟨i.val, h_lt⟩ = (-1 : ℤˣ) := by
        have h_last2 : (⟨i.val, h_lt⟩ : Fin (m + 1)) = Fin.last m := by
          apply Fin.ext
          change i.val = m
          omega
        have step1 : alt1_seq (m + 1) ⟨i.val, h_lt⟩ = alt1_seq (m + 1) (Fin.last m) :=
          congrArg (alt1_seq (m + 1)) h_last2
        have step2 : alt1_seq (m + 1) (Fin.last m) = (1 : ℤˣ) := alt1_seq_last m
        have step3 : alt1_seq (m + 1) ⟨i.val, h_lt⟩ = (1 : ℤˣ) := step1.trans step2
        exact step3.symm ▸ units_neg_one

      rw [eq1, eq_LHS]
      exact eq_RHS.symm

theorem alt_seq_in_sol (n : ℕ) :
  alt1_seq n ∈ putnam_2025_a5_solution n ∧ alt2_seq n ∈ putnam_2025_a5_solution n :=
by
  induction n with
  | zero =>
    exact ⟨sol_zero (alt1_seq 0), sol_zero (alt2_seq 0)⟩
  | succ n ih =>
    exact ⟨alt1_seq_in_sol_step n ih.right, alt2_seq_in_sol_step n ih.left⟩

theorem alt1_seq_1_eval : alt1_seq 1 (0 : Fin 1) = (1 : ℤˣ) :=
rfl

theorem alt2_seq_1_eval : alt2_seq 1 (0 : Fin 1) = (-1 : ℤˣ) :=
rfl

theorem sol_1_eq (s : Fin 1 → ℤˣ) : s = alt1_seq 1 ∨ s = alt2_seq 1 :=
by
  have h := Int.units_eq_one_or (s (0 : Fin 1))
  cases h with
  | inl h1 =>
    left
    apply funext
    intro i
    have hi : i = (0 : Fin 1) := Fin.ext (by omega)
    rw [hi, h1]
    exact alt1_seq_1_eval.symm
  | inr h2 =>
    right
    apply funext
    intro i
    have hi : i = (0 : Fin 1) := Fin.ext (by omega)
    rw [hi, h2]
    exact alt2_seq_1_eval.symm

theorem s_init_in_sol {m : ℕ} {s : Fin (m + 2) → ℤˣ}
  (hs : s ∈ putnam_2025_a5_solution (m + 2)) :
  (fun i : Fin (m + 1) => s (Fin.castSucc i)) ∈ putnam_2025_a5_solution (m + 1) :=
by
  intro i hi
  exact hs (Fin.castSucc i) (Nat.lt.step hi)

theorem putnam_2025_a5_solution_step {n : ℕ} {s : Fin n → ℤˣ}
  (hs : s ∈ putnam_2025_a5_solution n) (i : Fin n) (h : i.val + 1 < n) :
  s ⟨i.val + 1, h⟩ = - s i :=
hs i h

theorem s_last_eq {m : ℕ} {s : Fin (m + 2) → ℤˣ}
  (hs : s ∈ putnam_2025_a5_solution (m + 2)) :
  s (Fin.last (m + 1)) = - s (Fin.castSucc (Fin.last m)) :=
by
  -- The value of `Fin.castSucc (Fin.last m)` is `m`. Hence, its value + 1 is `m + 1`.
  -- We verify the hypothesis `m + 1 < m + 2`, which is definitionally `m + 1 < (m + 1) + 1`.
  have h_lt : (Fin.castSucc (Fin.last m) : Fin (m + 2)).val + 1 < m + 2 := Nat.lt_succ_self (m + 1)

  -- Instantiate the recurrence step from the sequence definition.
  have h_step := putnam_2025_a5_solution_step hs (Fin.castSucc (Fin.last m)) h_lt

  -- Show that `⟨m + 1, h_lt⟩` is definitionally equivalent to `Fin.last (m + 1)`.
  have h_eq : (⟨(Fin.castSucc (Fin.last m) : Fin (m + 2)).val + 1, h_lt⟩ : Fin (m + 2)) = Fin.last (m + 1) := rfl

  -- Substitute this definitional equivalence back into our recurrent equation.
  rw [h_eq] at h_step

  exact h_step

theorem seq_eq_from_parts {α : Type*} {m : ℕ} (s1 s2 : Fin (m + 1) → α)
  (h_cast : ∀ i : Fin m, s1 (Fin.castSucc i) = s2 (Fin.castSucc i))
  (h_last : s1 (Fin.last m) = s2 (Fin.last m)) :
  s1 = s2 :=
by
  ext x
  exact Fin.lastCases h_last h_cast x

theorem solution_eq_alt (m : ℕ) : ∀ (s : Fin (m + 1) → ℤˣ),
  s ∈ putnam_2025_a5_solution (m + 1) → s = alt1_seq (m + 1) ∨ s = alt2_seq (m + 1) :=
by
  induction m with
  | zero =>
    intro s _
    exact sol_1_eq s
  | succ d ih =>
    intro s hs
    have h_init : (fun i : Fin (d + 1) => s (Fin.castSucc i)) ∈ putnam_2025_a5_solution (d + 1) := s_init_in_sol hs
    have h_cases := ih (fun i => s (Fin.castSucc i)) h_init
    cases h_cases with
    | inl h1 =>
      right
      apply seq_eq_from_parts
      · intro i
        have h_s : s (Fin.castSucc i) = (fun j => s (Fin.castSucc j)) i := rfl
        rw [h_s, h1]
        have h_alt := alt2_seq_castSucc (d + 1)
        exact congrFun h_alt.symm i
      · have h_last_s : s (Fin.last (d + 1)) = - s (Fin.castSucc (Fin.last d)) := s_last_eq hs
        have h_s_cast : s (Fin.castSucc (Fin.last d)) = (fun j => s (Fin.castSucc j)) (Fin.last d) := rfl
        rw [h_s_cast, h1, alt1_seq_last d, units_neg_one] at h_last_s
        rw [h_last_s]
        exact (alt2_seq_last (d + 1)).symm
    | inr h2 =>
      left
      apply seq_eq_from_parts
      · intro i
        have h_s : s (Fin.castSucc i) = (fun j => s (Fin.castSucc j)) i := rfl
        rw [h_s, h2]
        have h_alt := alt1_seq_castSucc (d + 1)
        exact congrFun h_alt.symm i
      · have h_last_s : s (Fin.last (d + 1)) = - s (Fin.castSucc (Fin.last d)) := s_last_eq hs
        have h_s_cast : s (Fin.castSucc (Fin.last d)) = (fun j => s (Fin.castSucc j)) (Fin.last d) := rfl
        rw [h_s_cast, h2, alt2_seq_last d, units_neg_neg_one] at h_last_s
        rw [h_last_s]
        exact (alt1_seq_last (d + 1)).symm

theorem solution_iff (n : ℕ) (hn : 1 ≤ n) (s : Fin n → ℤˣ) :
  s ∈ putnam_2025_a5_solution n ↔ s = alt1_seq n ∨ s = alt2_seq n :=
by
  constructor
  · intro hs
    cases n
    case zero => omega
    case succ k => exact solution_eq_alt k s hs
  · rintro (rfl | rfl)
    · exact (alt_seq_in_sol n).1
    · exact (alt_seq_in_sol n).2

theorem neg_one_ne_one_units_int : (-1 : ℤˣ) ≠ (1 : ℤˣ) :=
by
  decide

theorem V_zero_eval_alt2 : V 0 (alt2_seq 0) = V_alt2 0 :=
rfl

theorem V_succ_eq_I (d : ℕ) (s : Fin (d + 1) → ℤˣ) (h : s (Fin.last d) = (1 : ℤˣ)) (k : Fin (d + 2)) :
  V (d + 1) s k = I d (V d (fun i => s (Fin.castSucc i))) k :=
by
  -- Unfold the definition of V and use the hypothesis `h` to evaluate the
  -- `if-then-else` condition directly to the true branch.
  simp [V, h]

theorem V_succ_eq_J (d : ℕ) (s : Fin (d + 1) → ℤˣ) (h : s (Fin.last d) ≠ (1 : ℤˣ)) (k : Fin (d + 2)) :
  V (d + 1) s k = J d (V d (fun i => s (Fin.castSucc i))) k :=
by
  -- Explicitly reduce the left-hand side exactly 1 level by definitional equality, avoiding unfolding `V d` on the RHS
  have h_eq : V (d + 1) s k = (if s (Fin.last d) = (1 : ℤˣ) then I d (V d (fun i => s (Fin.castSucc i))) else J d (V d (fun i => s (Fin.castSucc i)))) k := rfl
  rw [h_eq]
  -- Resolve the if-statement using our negative hypothesis `h`
  rw [if_neg h]

theorem V_zero_eval_alt1 : V 0 (alt1_seq 0) = V_alt1 0 :=
rfl

theorem V_eq_alt1_and_alt2 (n : ℕ) : V n (alt1_seq n) = V_alt1 n ∧ V n (alt2_seq n) = V_alt2 n :=
by
  induction n with
  | zero =>
    constructor
    · exact V_zero_eval_alt1
    · exact V_zero_eval_alt2
  | succ d ih =>
    have ih1 := ih.1
    have ih2 := ih.2
    constructor
    · ext k
      -- Goal 1: Compute for `alt1_seq`
      rw [V_succ_eq_I d (alt1_seq (d + 1)) (alt1_seq_last d) k]
      rw [alt1_seq_castSucc d]
      rw [ih2]
      rw [I_V_alt2_eq d k]
    · ext k
      -- Goal 2: Compute for `alt2_seq`
      have h_last : alt2_seq (d + 1) (Fin.last d) ≠ (1 : ℤˣ) := by
        rw [alt2_seq_last d]
        exact neg_one_ne_one_units_int
      rw [V_succ_eq_J d (alt2_seq (d + 1)) h_last k]
      rw [alt2_seq_castSucc d]
      rw [ih1]
      rw [J_V_alt1_eq d k]

theorem V_eq_alt1 (n : ℕ) : V n (alt1_seq n) = V_alt1 n :=
(V_eq_alt1_and_alt2 n).left

theorem V_succ_eval_alt2 (d : ℕ) :
  V (d + 1) (alt2_seq (d + 1)) =
    if alt2_seq (d + 1) (Fin.last d) = (1 : ℤˣ) then
      I d (V d (fun i => alt2_seq (d + 1) (Fin.castSucc i)))
    else
      J d (V d (fun i => alt2_seq (d + 1) (Fin.castSucc i))) :=
rfl

theorem V_alt2_succ_eval (d : ℕ) : V_alt2 (d + 1) = J d (V_alt1 d) :=
rfl

theorem V_eq_alt2 (n : ℕ) : V n (alt2_seq n) = V_alt2 n :=
by
  cases n with
  | zero =>
    change V 0 (alt2_seq 0) = V_alt2 0
    exact V_zero_eval_alt2
  | succ d =>
    change V (d + 1) (alt2_seq (d + 1)) = V_alt2 (d + 1)
    rw [V_succ_eval_alt2 d]
    rw [alt2_seq_last d]
    rw [if_neg neg_one_ne_one_units_int]
    rw [alt2_seq_castSucc d]
    rw [V_eq_alt1 d]
    rw [← V_alt2_succ_eval d]

theorem V_zero_le_V_alt1 (s : Fin 0 → ℤˣ) (k : Fin 1) : V 0 s k ≤ V_alt1 0 k :=
Nat.le_refl 1

theorem I_mono {n : ℕ} {A B : Fin (n + 1) → ℕ} (h : ∀ k, A k ≤ B k) : ∀ k, I n A k ≤ I n B k :=
by
  intro k
  unfold I
  apply sum_le_sum
  intro i _
  split_ifs
  · exact h i
  · omega

theorem J_V_alt2_le_J_V_alt1_zero (k : Fin (0 + 2)) :
  J 0 (V_alt2 0) k ≤ J 0 (V_alt1 0) k :=
le_rfl

theorem J_eq_sum (n : ℕ) (A : Fin (n + 1) → ℕ) (k : Fin (n + 2)) :
  J n A k = Finset.sum Finset.univ (fun i => if k.val ≤ i.val then A i else 0) :=
rfl

theorem J_anti_mono_term (n : ℕ) (A : Fin (n + 1) → ℕ) (i j : Fin (n + 2)) (hij : i.val ≤ j.val) (k : Fin (n + 1)) :
  (if j.val ≤ k.val then A k else 0) ≤ (if i.val ≤ k.val then A k else 0) :=
by
  split <;> split <;> omega

theorem J_anti_mono (n : ℕ) (A : Fin (n + 1) → ℕ) (i j : Fin (n + 2)) (hij : i.val ≤ j.val) :
  J n A j ≤ J n A i :=
by
  rw [J_eq_sum, J_eq_sum]
  apply Finset.sum_le_sum
  intro k _
  exact J_anti_mono_term n A i j hij k

theorem V_alt2_anti_mono (d : ℕ) (i j : Fin (Nat.succ d + 1)) (hij : i.val ≤ j.val) :
  V_alt2 (Nat.succ d) j ≤ V_alt2 (Nat.succ d) i :=
by
  have hd : V_alt2 (Nat.succ d) = J d (V_alt1 d) := by
    -- Using `change` ensures we explicitly unify `Nat.succ d` and `d + 1` definitionally
    change V_alt2 (d + 1) = J d (V_alt1 d)
    exact V_alt2_succ_eval d
  rw [hd]
  exact J_anti_mono d (V_alt1 d) i j hij

theorem V_alt1_eq_comp_rev_alt2 (d : ℕ) :
  V_alt1 (Nat.succ d) = fun (x : Fin (Nat.succ d + 1)) => V_alt2 (Nat.succ d) x.rev :=
by
  ext x
  -- V_alt2 (Nat.succ d) x.rev rewrites to V_alt1 (Nat.succ d) x.rev.rev
  -- by the known relationship between V_alt2 and V_alt1.
  -- Then x.rev.rev simply simplifies to x by the involutive property of reversal.
  rw [V_alt2_eq_rev, fin_rev_rev]

theorem J_rev_eq_I_rev {n : ℕ} (A : Fin (n + 1) → ℕ) (k : Fin (n + 2)) :
  J n (fun i => A i.rev) k = I n A k.rev :=
by
  rw [J_eq_sum_filter]
  rw [I_eq_sum_filter]
  apply sum_filter_eq_sum_filter_rev
  intro j
  rfl

theorem F2_to_F1_fun_val (n : ℕ) (k : Fin (n + 2)) (x : Fin (n + 1))
  (hx : (x : ℕ) < (k.rev : ℕ)) :
  (F2_to_F1_fun n k x : ℕ) = (x : ℕ) + (k : ℕ) :=
by
  -- Expand the definition of the function to expose the `dite` statement.
  unfold F2_to_F1_fun

  -- Split into the positive and negative branches of the `if-then-else`.
  split
  · -- Case 1: The condition ((x : ℕ) + (k : ℕ) < n + 1) is True.
    -- The evaluated value `⟨(x : ℕ) + (k : ℕ), h⟩` coerces to exactly `(x : ℕ) + (k : ℕ)`.
    rfl
  · -- Case 2: The condition is False. We must establish a contradiction.
    rename_i h
    exfalso
    -- We simplify the reversed Fin element in our hypothesis `hx`.
    -- The `simp` tactic applies `Fin.val_rev`, converting `(k.rev : ℕ)` to `(n + 2) - 1 - (k : ℕ)`.
    simp at hx
    -- With all expressions cleanly mapped to pure `ℕ` linear arithmetic,
    -- `omega` naturally deduces the contradiction from `k < n + 2` and our bounds.
    omega

theorem F2_to_F1_fun_mem (n : ℕ) (k : Fin (n + 2)) (x : Fin (n + 1))
  (hx : x ∈ Finset.filter (fun j : Fin (n + 1) => (j : ℕ) < (k.rev : ℕ)) Finset.univ) :
  F2_to_F1_fun n k x ∈ Finset.filter (fun j : Fin (n + 1) => (k : ℕ) ≤ (j : ℕ)) Finset.univ :=
by
  -- Unpack the filter definitions for both the hypothesis and the goal
  rw [Finset.mem_filter] at hx ⊢
  rcases hx with ⟨_, hx_lt⟩

  -- The first part of the goal is trivial (membership in Finset.univ)
  refine ⟨Finset.mem_univ _, ?_⟩

  -- Perform beta-reduction on the filter condition
  dsimp only

  -- Substitute the value of F2_to_F1_fun using our helper lemma
  rw [F2_to_F1_fun_val n k x hx_lt]

  -- The remaining goal `k.val ≤ x.val + k.val` is trivial over ℕ
  omega

theorem F2_to_F1_fun_inj (n : ℕ) (k : Fin (n + 2)) (x y : Fin (n + 1))
  (hx : x ∈ Finset.filter (fun j : Fin (n + 1) => (j : ℕ) < (k.rev : ℕ)) Finset.univ)
  (hy : y ∈ Finset.filter (fun j : Fin (n + 1) => (j : ℕ) < (k.rev : ℕ)) Finset.univ)
  (h : F2_to_F1_fun n k x = F2_to_F1_fun n k y) : x = y :=
by
  -- Extract the upper bound condition from the filter membership
  rw [Finset.mem_filter] at hx hy

  -- Evaluate F2_to_F1_fun for x and y using the helper lemma
  have h1 := F2_to_F1_fun_val n k x hx.2
  have h2 := F2_to_F1_fun_val n k y hy.2

  -- Transfer the equality given by hypothesis `h` to the natural number domain
  have h3 : (F2_to_F1_fun n k x : ℕ) = (F2_to_F1_fun n k y : ℕ) := by rw [h]

  -- Use extensionality to reduce `x = y` in Fin(n+1) to their natural number values
  apply Fin.ext

  -- Solve the resulting linear arithmetic equality: (x : ℕ) + (k : ℕ) = (y : ℕ) + (k : ℕ)
  omega

theorem F2_to_F1_fun_surj (n : ℕ) (k : Fin (n + 2)) (y : Fin (n + 1))
  (hy : y ∈ Finset.filter (fun j : Fin (n + 1) => (k : ℕ) ≤ (j : ℕ)) Finset.univ) :
  ∃ x, ∃ hx : x ∈ Finset.filter (fun j : Fin (n + 1) => (j : ℕ) < (k.rev : ℕ)) Finset.univ,
    F2_to_F1_fun n k x = y :=
by
  have hk_le_y : (k : ℕ) ≤ (y : ℕ) := by
    rw [Finset.mem_filter] at hy
    exact hy.2
  have hy_lt : (y : ℕ) < n + 1 := y.isLt
  have hx_lt_n1 : (y : ℕ) - (k : ℕ) < n + 1 := by omega

  let x : Fin (n + 1) := ⟨(y : ℕ) - (k : ℕ), hx_lt_n1⟩
  have h_x_val : (x : ℕ) = (y : ℕ) - (k : ℕ) := rfl

  have hx_lt_k_rev : (x : ℕ) < (k.rev : ℕ) := by
    -- Automatically brings the evaluation of `(k.rev : ℕ)` as a hypothesis into context
    have hk_rev_eq := Fin.val_rev k
    omega

  have hx_mem : x ∈ Finset.filter (fun j : Fin (n + 1) => (j : ℕ) < (k.rev : ℕ)) Finset.univ := by
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ x, hx_lt_k_rev⟩

  use x, hx_mem
  apply Fin.ext

  have h_val : (F2_to_F1_fun n k x : ℕ) = (x : ℕ) + (k : ℕ) := F2_to_F1_fun_val n k x hx_lt_k_rev
  rw [h_val, h_x_val]
  omega

theorem sum_A_F2_to_F1_eq_sum_A_F1 (n : ℕ) (A : Fin (n + 1) → ℕ) (k : Fin (n + 2)) :
  Finset.sum (Finset.filter (fun j : Fin (n + 1) => (j : ℕ) < (k.rev : ℕ)) Finset.univ) (fun x => A (F2_to_F1_fun n k x)) =
  Finset.sum (Finset.filter (fun j : Fin (n + 1) => (k : ℕ) ≤ (j : ℕ)) Finset.univ) A :=
Finset.sum_bij (fun x _ => F2_to_F1_fun n k x)
    (fun a ha => F2_to_F1_fun_mem n k a ha)
    (fun a1 ha1 a2 ha2 h => F2_to_F1_fun_inj n k a1 a2 ha1 ha2 h)
    (fun b hb => F2_to_F1_fun_surj n k b hb)
    (fun a _ => rfl)

theorem F2_to_F1_fun_eval (n : ℕ) (k : Fin (n + 2)) (x : Fin (n + 1))
  (hx : (x : ℕ) < (k.rev : ℕ)) :
  (F2_to_F1_fun n k x : ℕ) = (x : ℕ) + (k : ℕ) :=
by
  -- Use the standard mathlib lemma for the arithmetic property of Fin.rev
  have hk : (k.rev : ℕ) + (k : ℕ) = n + 1 := Fin.rev_add_cast k

  -- Expand the definition of F2_to_F1_fun which branches on `(x : ℕ) + (k : ℕ) < n + 1`
  unfold F2_to_F1_fun
  split
  · -- Case 1: The condition is true, so it evaluates to its positive branch.
    rfl
  · -- Case 2: The condition is false, which contradicts our hypotheses `hx` and `hk`.
    omega

theorem x_le_F2_to_F1_fun (n : ℕ) (k : Fin (n + 2)) (x : Fin (n + 1))
  (hx : (x : ℕ) < (k.rev : ℕ)) :
  (x : ℕ) ≤ (F2_to_F1_fun n k x : ℕ) :=
by
  rw [F2_to_F1_fun_eval n k x hx]
  omega

theorem sum_A_F2_to_F1_le_sum_A_F2 (n : ℕ) (A : Fin (n + 1) → ℕ)
  (hA : ∀ i j : Fin (n + 1), i.val ≤ j.val → A j ≤ A i) (k : Fin (n + 2)) :
  Finset.sum (Finset.filter (fun j : Fin (n + 1) => (j : ℕ) < (k.rev : ℕ)) Finset.univ) (fun x => A (F2_to_F1_fun n k x)) ≤
  Finset.sum (Finset.filter (fun j : Fin (n + 1) => (j : ℕ) < (k.rev : ℕ)) Finset.univ) A :=
by
  -- Strip away the sum and reduce the goal to proving the inequality point-wise
  apply Finset.sum_le_sum
  intro x hx
  -- Extract the boolean condition from the filter constraint
  rw [Finset.mem_filter] at hx
  -- Use the antitone property of A (this reduces the goal to proving the index bound)
  apply hA
  -- Apply our lemma which handles the bound for the true branch of F2_to_F1_fun
  exact x_le_F2_to_F1_fun n k x hx.2

theorem J_le_I_rev (n : ℕ) (A : Fin (n + 1) → ℕ) (hA : ∀ i j : Fin (n + 1), i.val ≤ j.val → A j ≤ A i) (k : Fin (n + 2)) :
  J n A k ≤ I n A k.rev :=
by
  -- 1. Expand custom sum operations into standard Finset.sum forms using available definitions
  rw [J_eq_sum_filter n A k]
  rw [I_eq_sum_filter n A k.rev]

  -- 2. Inject the bridging equality and inequality lemmas into the context
  have h_eq := sum_A_F2_to_F1_eq_sum_A_F1 n A k
  have h_le := sum_A_F2_to_F1_le_sum_A_F2 n A hA k

  -- 3. Resolve logically: write the equality mapping backwards, translating the J sum sequence directly into the I bounds
  rw [← h_eq]
  exact h_le

theorem J_le_J_rev {n : ℕ} (A : Fin (n + 1) → ℕ) (hA : ∀ i j : Fin (n + 1), i.val ≤ j.val → A j ≤ A i) (k : Fin (n + 2)) :
  J n A k ≤ J n (fun (x : Fin (n + 1)) => A x.rev) k :=
by
  have h := J_rev_eq_I_rev A k
  rw [h]
  exact J_le_I_rev n A hA k

theorem J_V_alt2_le_J_V_alt1_succ (d : ℕ) (k : Fin (Nat.succ d + 2)) :
  J (Nat.succ d) (V_alt2 (Nat.succ d)) k ≤ J (Nat.succ d) (V_alt1 (Nat.succ d)) k :=
by
  have H1 := V_alt2_anti_mono d
  have H2 := J_le_J_rev (V_alt2 (Nat.succ d)) H1 k
  rw [V_alt1_eq_comp_rev_alt2 d]
  exact H2

theorem J_V_alt2_le_J_V_alt1 (n : ℕ) (k : Fin (n + 2)) : J n (V_alt2 n) k ≤ J n (V_alt1 n) k :=
by
  cases n with
  | zero => exact J_V_alt2_le_J_V_alt1_zero k
  | succ d => exact J_V_alt2_le_J_V_alt1_succ d k

theorem I_add_J_pointwise (n : ℕ) (A : Fin (n + 1) → ℕ) (k : Fin (n + 2)) (j : Fin (n + 1)) :
  (if (j : ℕ) < (k : ℕ) then A j else 0) + (if (k : ℕ) ≤ (j : ℕ) then A j else 0) = A j :=
by
  split_ifs <;> omega

theorem I_add_J_eq_SumA (n : ℕ) (A : Fin (n + 1) → ℕ) (k : Fin (n + 2)) :
  I n A k + J n A k = SumA n A :=
by
  -- Convert custom functions to standard Finset sums using available lemmas
  rw [I_eq_sum_filter, J_eq_sum_filter, SumA_eq_sum]

  -- Rewrite filtered sums to conditional sums over the entire set
  simp_rw [Finset.sum_filter]

  -- Combine the split sums into a single sum
  rw [← Finset.sum_add_distrib]

  -- Focus on the inner contents of the sum
  apply Finset.sum_congr rfl
  intro j _

  -- Apply the pointwise evaluation helper lemma
  exact I_add_J_pointwise n A k j

theorem I_V_alt1_le_I_V_alt2 (n : ℕ) (k : Fin (n + 2)) : I n (V_alt1 n) k ≤ I n (V_alt2 n) k :=
by
  have h1 := I_add_J_eq_SumA n (V_alt1 n) k
  have h2 := I_add_J_eq_SumA n (V_alt2 n) k
  have h3 := SumA_V_alt1_eq_SumA_V_alt2 n
  have h4 := J_V_alt2_le_J_V_alt1 n k
  omega

theorem V_le_alt_step_I (d : ℕ) (V_prev : Fin (d + 1) → ℕ)
  (h_ind : (∀ k : Fin (d + 1), V_prev k ≤ V_alt1 d k) ∨ (∀ k : Fin (d + 1), V_prev k ≤ V_alt2 d k)) :
  ∀ k : Fin (d + 2), I d V_prev k ≤ V_alt1 (d + 1) k :=
by
  intro k
  cases h_ind with
  | inl h1 =>
    rw [← I_V_alt2_eq d k]
    exact le_trans (I_mono h1 k) (I_V_alt1_le_I_V_alt2 d k)
  | inr h2 =>
    rw [← I_V_alt2_eq d k]
    exact I_mono h2 k

theorem J_term_mono {n : ℕ} {A B : Fin (n + 1) → ℕ} (h : ∀ k, A k ≤ B k) (k : Fin (n + 2)) (i : Fin (n + 1)) :
  (if k.val ≤ i.val then A i else 0) ≤ (if k.val ≤ i.val then B i else 0) :=
by
  split_ifs
  · exact h i
  · exact le_rfl

theorem J_mono {n : ℕ} {A B : Fin (n + 1) → ℕ} (h : ∀ k, A k ≤ B k) : ∀ k, J n A k ≤ J n B k :=
by
  intro k
  rw [J_eq_sum n A k, J_eq_sum n B k]
  apply Finset.sum_le_sum
  intro i _
  exact J_term_mono h k i

theorem V_le_alt_step_J (d : ℕ) (V_prev : Fin (d + 1) → ℕ)
  (h_ind : (∀ k : Fin (d + 1), V_prev k ≤ V_alt1 d k) ∨ (∀ k : Fin (d + 1), V_prev k ≤ V_alt2 d k)) :
  ∀ k : Fin (d + 2), J d V_prev k ≤ V_alt2 (d + 1) k :=
by
  intro k
  rw [V_alt2_succ_eval d]
  cases h_ind with
  | inl h =>
    exact J_mono h k
  | inr h =>
    exact le_trans (J_mono h k) (J_V_alt2_le_J_V_alt1 d k)

theorem V_le_alt (n : ℕ) (s : Fin n → ℤˣ) : (∀ k, V n s k ≤ V_alt1 n k) ∨ (∀ k, V n s k ≤ V_alt2 n k) :=
by
  revert s
  induction n with
  | zero =>
    intro s
    left
    intro k
    exact V_zero_le_V_alt1 s k
  | succ d hd =>
    intro s
    by_cases h : s (Fin.last d) = (1 : ℤˣ)
    · left
      intro k
      rw [V_succ_eq_I d s h k]
      exact V_le_alt_step_I d _ (hd (fun i => s (Fin.castSucc i))) k
    · right
      intro k
      rw [V_succ_eq_J d s h k]
      exact V_le_alt_step_J d _ (hd (fun i => s (Fin.castSucc i))) k

theorem fin1_eq_zero (i : Fin 1) : i = 0 :=
by
  ext
  omega

theorem fin1_zsq_eq_alt1_or_alt2 (s : Fin 1 → ℤˣ) : s = alt1_seq 1 ∨ s = alt2_seq 1 :=
by
  have h := Int.units_eq_one_or (s (0 : Fin 1))
  rcases h with h1 | h2
  · left
    funext i
    have h_i : i = (0 : Fin 1) := fin1_eq_zero i
    rw [h_i, h1]
    exact alt1_seq_1_eval.symm
  · right
    funext i
    have h_i : i = (0 : Fin 1) := fin1_eq_zero i
    rw [h_i, h2]
    exact alt2_seq_1_eval.symm

theorem V_sum_lt_alt_base (s : Fin 1 → ℤˣ) (h1 : s ≠ alt1_seq 1) (h2 : s ≠ alt2_seq 1) :
  SumA 1 (V 1 s) < SumA 1 (V_alt1 1) :=
by
  match fin1_zsq_eq_alt1_or_alt2 s with
  | Or.inl heq => exact False.elim (h1 heq)
  | Or.inr heq => exact False.elim (h2 heq)

theorem units_int_ne_one_implies_eq_neg_one (x : ℤˣ) (h : x ≠ (1 : ℤˣ)) : x = (-1 : ℤˣ) :=
by
  have h_or : x = 1 ∨ x = -1 := Int.units_eq_one_or x
  cases h_or with
  | inl h1 => exact False.elim (h h1)
  | inr h2 => exact h2

theorem s_eq_alt1_of_prev_eq_alt2_and_last_eq_one {d : ℕ} (s : Fin (d + 1) → ℤˣ)
  (h_prev : (fun i : Fin d => s (Fin.castSucc i)) = alt2_seq d)
  (h_last : s (Fin.last d) = (1 : ℤˣ)) : s = alt1_seq (d + 1) :=
by
  ext i
  refine Fin.lastCases ?_ ?_ i
  · rw [h_last, alt1_seq_last d]
  · intro j
    have h1 : s (Fin.castSucc j) = alt2_seq d j := congr_fun h_prev j
    have h2 : alt1_seq (d + 1) (Fin.castSucc j) = alt2_seq d j := congr_fun (alt1_seq_castSucc d) j
    rw [h1, h2]

theorem s_eq_alt2_of_prev_eq_alt1_and_last_eq_neg_one {d : ℕ} (s : Fin (d + 1) → ℤˣ)
  (h_prev : (fun i : Fin d => s (Fin.castSucc i)) = alt1_seq d)
  (h_last : s (Fin.last d) = (-1 : ℤˣ)) : s = alt2_seq (d + 1) :=
by
  -- Apply function extensionality, then rewrite using the structural property of Fin
  ext x
  revert x
  rw [Fin.forall_iff_castSucc]
  constructor
  · -- Case 1: Evaluate at `Fin.last d`
    rw [h_last, alt2_seq_last]
  · -- Case 2: Evaluate at `Fin.castSucc i` for an arbitrary `i : Fin d`
    intro i
    have h1 : s (Fin.castSucc i) = alt1_seq d i := congr_fun h_prev i
    have h2 : alt2_seq (d + 1) (Fin.castSucc i) = alt1_seq d i := congr_fun (alt2_seq_castSucc d) i
    rw [h1, h2]

theorem SumA_mono {n : ℕ} {A B : Fin (n + 1) → ℕ} (h : ∀ k, A k ≤ B k) : SumA n A ≤ SumA n B :=
by
  unfold SumA
  apply Finset.sum_le_sum
  intro i _
  exact h i

theorem SumA_I_eq_sum_double (d : ℕ) (A : Fin (d + 1) → ℕ) :
  SumA (d + 1) (I d A) = Finset.sum Finset.univ (fun (k : Fin (d + 2)) =>
    Finset.sum Finset.univ (fun (i : Fin (d + 1)) => if (i : ℕ) < (k : ℕ) then A i else 0)) :=
by
  rfl

theorem ite_one_mul_nat (P : Prop) [Decidable P] (a : ℕ) :
  (if P then (1 : ℕ) else (0 : ℕ)) * a = if P then a else (0 : ℕ) :=
by
  by_cases h : P
  · simp [h]
  · simp [h]

theorem I_coeff_eq_sum (d : ℕ) (i : Fin (d + 1)) :
  I_coeff d i = Finset.sum Finset.univ (fun (k : Fin (d + 2)) => if (i : ℕ) < (k : ℕ) then (1 : ℕ) else (0 : ℕ)) :=
rfl

theorem I_coeff_mul_A_eq (d : ℕ) (i : Fin (d + 1)) (A : Fin (d + 1) → ℕ) :
  Finset.sum Finset.univ (fun (k : Fin (d + 2)) => if (i : ℕ) < (k : ℕ) then A i else 0) = I_coeff d i * A i :=
by
  -- Rewrite the right-hand side using the summation definition for `I_coeff d i`
  rw [I_coeff_eq_sum d i]
  -- Distribute the multiplication of `A i` inside the `Finset.sum`
  rw [Finset.sum_mul]
  -- Show that the arguments of the sum are exactly equivalent for all `k`
  apply Finset.sum_congr rfl
  intro k _
  -- Apply our helper lemma to formally close the equality equivalence
  exact (ite_one_mul_nat ((i : ℕ) < (k : ℕ)) (A i)).symm

theorem SumA_I_eq_sum_I_coeff (d : ℕ) (A : Fin (d + 1) → ℕ) :
  SumA (d + 1) (I d A) = Finset.sum Finset.univ (fun (i : Fin (d + 1)) => I_coeff d i * A i) :=
by
  rw [SumA_I_eq_sum_double, Finset.sum_comm]
  exact Finset.sum_congr rfl (fun i _ => I_coeff_mul_A_eq d i A)

theorem I_coeff_term_last (d : ℕ) (i : Fin (d + 1)) :
  (if (i : ℕ) < ((Fin.last (d + 1)) : ℕ) then (1 : ℕ) else (0 : ℕ)) = 1 :=
by
  have h : (i : ℕ) < ((Fin.last (d + 1)) : ℕ) := i.isLt
  exact if_pos h

theorem I_coeff_pos (d : ℕ) (i : Fin (d + 1)) : 0 < I_coeff d i :=
by
  rw [I_coeff_eq_sum]
  have h_le : (if (i : ℕ) < ((Fin.last (d + 1)) : ℕ) then (1 : ℕ) else (0 : ℕ)) ≤
    Finset.sum Finset.univ (fun (k : Fin (d + 2)) => if (i : ℕ) < (k : ℕ) then (1 : ℕ) else (0 : ℕ)) := by
    exact Finset.single_le_sum_of_canonicallyOrdered
      (f := fun (k : Fin (d + 2)) => if (i : ℕ) < (k : ℕ) then (1 : ℕ) else (0 : ℕ))
      (i := Fin.last (d + 1))
      (Finset.mem_univ (Fin.last (d + 1)))
  rw [I_coeff_term_last d i] at h_le
  omega

theorem exists_lt_of_sum_lt {d : ℕ} {A B : Fin (d + 1) → ℕ}
  (h_le : ∀ i, A i ≤ B i) (h_lt : SumA d A < SumA d B) :
  ∃ i ∈ (Finset.univ : Finset (Fin (d + 1))), A i < B i :=
by
  by_contra h_contra
  push_neg at h_contra
  have hab : A = B := by
    funext i
    have h1 := h_le i
    have h2 := h_contra i (Finset.mem_univ i)
    omega
  rw [hab] at h_lt
  omega

theorem I_strict_mono {d : ℕ} {A B : Fin (d + 1) → ℕ} (h_le : ∀ i, A i ≤ B i) (h_lt : SumA d A < SumA d B) :
  SumA (d + 1) (I d A) < SumA (d + 1) (I d B) :=
by
  -- Rewrite sums in terms of explicit coefficients
  rw [SumA_I_eq_sum_I_coeff d A, SumA_I_eq_sum_I_coeff d B]

  -- Upgrade pointwise inequality into strict summation inequality
  apply Finset.sum_lt_sum
  · -- Subgoal 1: Prove pointwise ≤ for all elements
    intro i _
    exact Nat.mul_le_mul_left (I_coeff d i) (h_le i)
  · -- Subgoal 2: Extract index demonstrating strict < for at least one element
    rcases exists_lt_of_sum_lt h_le h_lt with ⟨i, hi, h_lt_i⟩
    exact ⟨i, hi, Nat.mul_lt_mul_of_pos_left h_lt_i (I_coeff_pos d i)⟩

theorem V_sum_lt_alt_step_I_valid (d : ℕ) (A : Fin (d + 1) → ℕ)
  (h_le : (∀ k, A k ≤ V_alt1 d k) ∨ (∀ k, A k ≤ V_alt2 d k))
  (h_lt : SumA d A < SumA d (V_alt1 d)) :
  SumA (d + 1) (I d A) < SumA (d + 1) (V_alt1 (d + 1)) :=
by
  cases h_le with
  | inl h_alt1 =>
    have h1 := I_strict_mono h_alt1 h_lt
    have h2 := SumA_mono (I_V_alt1_le_I_V_alt2 d)
    have h3 : I d (V_alt2 d) = V_alt1 (d + 1) := funext (I_V_alt2_eq d)
    rw [h3] at h2
    exact lt_of_lt_of_le h1 h2
  | inr h_alt2 =>
    have heq := SumA_V_alt1_eq_SumA_V_alt2 d
    have h_lt2 : SumA d A < SumA d (V_alt2 d) := by
      rw [← heq]
      exact h_lt
    have h1 := I_strict_mono h_alt2 h_lt2
    have h3 : I d (V_alt2 d) = V_alt1 (d + 1) := funext (I_V_alt2_eq d)
    rw [h3] at h1
    exact h1

theorem J_zero_eq_SumA (d : ℕ) (A : Fin (d + 1) → ℕ) :
  J d A 0 = SumA d A :=
by
  -- Explicitly state the defeq evaluation of J and SumA
  change Finset.sum Finset.univ (fun (i : Fin (d + 1)) => if (0 : Fin (d + 2)).val ≤ i.val then A i else 0) = Finset.sum Finset.univ (fun (k : Fin (d + 1)) => A k)

  -- Apply congruence over the sum index
  apply Finset.sum_congr rfl
  intro i _

  -- Prove the filtering condition is trivially true (0 ≤ i)
  have h : (0 : Fin (d + 2)).val ≤ i.val := Nat.zero_le i.val

  -- Resolve the if-else loop to exactly the array value
  exact if_pos h

theorem sum_strict_mono_of_0_lt_of_le {d : ℕ} {f g : Fin (d + 2) → ℕ}
  (h0 : f 0 < g 0) (hle : ∀ k, f k ≤ g k) :
  Finset.sum Finset.univ f < Finset.sum Finset.univ g :=
by
  apply Finset.sum_lt_sum
  · intro i _
    exact hle i
  · exact ⟨0, Finset.mem_univ 0, h0⟩

theorem SumA_J_strict_mono {d : ℕ} {A B : Fin (d + 1) → ℕ}
  (h_le : ∀ k, A k ≤ B k) (h_lt : SumA d A < SumA d B) :
  SumA (d + 1) (J d A) < SumA (d + 1) (J d B) :=
by
  rw [SumA_eq_sum (d + 1) (J d A), SumA_eq_sum (d + 1) (J d B)]
  apply sum_strict_mono_of_0_lt_of_le
  · rw [J_zero_eq_SumA d A, J_zero_eq_SumA d B]
    exact h_lt
  · exact J_mono h_le

theorem V_sum_lt_alt_step_J_valid (d : ℕ) (A : Fin (d + 1) → ℕ)
  (h_le : (∀ k, A k ≤ V_alt1 d k) ∨ (∀ k, A k ≤ V_alt2 d k))
  (h_lt : SumA d A < SumA d (V_alt1 d)) :
  SumA (d + 1) (J d A) < SumA (d + 1) (V_alt1 (d + 1)) :=
by
  cases h_le with
  | inl h1 =>
    have h_strict : SumA (d + 1) (J d A) < SumA (d + 1) (J d (V_alt1 d)) := SumA_J_strict_mono h1 h_lt
    have h_eq1 : J d (V_alt1 d) = V_alt2 (d + 1) := (V_alt2_succ_eval d).symm
    have h_eq1_congr : SumA (d + 1) (J d (V_alt1 d)) = SumA (d + 1) (V_alt2 (d + 1)) := congrArg (SumA (d + 1)) h_eq1
    have h_eq2 : SumA (d + 1) (V_alt2 (d + 1)) = SumA (d + 1) (V_alt1 (d + 1)) := (SumA_V_alt1_eq_SumA_V_alt2 (d + 1)).symm
    calc
      SumA (d + 1) (J d A) < SumA (d + 1) (J d (V_alt1 d)) := h_strict
      _ = SumA (d + 1) (V_alt2 (d + 1)) := h_eq1_congr
      _ = SumA (d + 1) (V_alt1 (d + 1)) := h_eq2
  | inr h2 =>
    have h_lt2 : SumA d A < SumA d (V_alt2 d) := by
      calc
        SumA d A < SumA d (V_alt1 d) := h_lt
        _ = SumA d (V_alt2 d) := SumA_V_alt1_eq_SumA_V_alt2 d
    have h_strict : SumA (d + 1) (J d A) < SumA (d + 1) (J d (V_alt2 d)) := SumA_J_strict_mono h2 h_lt2
    have h_le3 : SumA (d + 1) (J d (V_alt2 d)) ≤ SumA (d + 1) (J d (V_alt1 d)) := SumA_mono (J_V_alt2_le_J_V_alt1 d)
    have h_eq1 : J d (V_alt1 d) = V_alt2 (d + 1) := (V_alt2_succ_eval d).symm
    have h_eq1_congr : SumA (d + 1) (J d (V_alt1 d)) = SumA (d + 1) (V_alt2 (d + 1)) := congrArg (SumA (d + 1)) h_eq1
    have h_eq2 : SumA (d + 1) (V_alt2 (d + 1)) = SumA (d + 1) (V_alt1 (d + 1)) := (SumA_V_alt1_eq_SumA_V_alt2 (d + 1)).symm
    calc
      SumA (d + 1) (J d A) < SumA (d + 1) (J d (V_alt2 d)) := h_strict
      _ ≤ SumA (d + 1) (J d (V_alt1 d)) := h_le3
      _ = SumA (d + 1) (V_alt2 (d + 1)) := h_eq1_congr
      _ = SumA (d + 1) (V_alt1 (d + 1)) := h_eq2

theorem V_alt2_zero_pos_base_for_V_sum_I : 0 < V_alt2 0 ⟨0, Nat.zero_lt_succ 0⟩ :=
Nat.zero_lt_one

theorem J_zero_eq_SumA_for_V_sum_I (n : ℕ) (A : Fin (n + 1) → ℕ) :
  J n A ⟨0, Nat.zero_lt_succ (n + 1)⟩ = SumA n A :=
by
  simp [J, SumA]

theorem SumA_ge_eval_zero_for_V_sum_I (n : ℕ) (A : Fin (n + 1) → ℕ) :
  A ⟨0, Nat.zero_lt_succ n⟩ ≤ SumA n A :=
by
  rw [SumA_eq_sum]
  apply Finset.single_le_sum
  · intro i _
    exact Nat.zero_le (A i)
  · exact Finset.mem_univ _

theorem V_alt2_zero_pos_for_V_sum_I (d : ℕ) :
  0 < V_alt2 d ⟨0, Nat.zero_lt_succ d⟩ :=
by
  induction d with
  | zero =>
    -- Base Case: d = 0
    exact V_alt2_zero_pos_base_for_V_sum_I
  | succ n ih =>
    -- Inductive Step: d = n + 1
    -- Explicitly format the goal to use (n + 1) which aligns with definitions.
    change 0 < V_alt2 (n + 1) ⟨0, Nat.zero_lt_succ (n + 1)⟩

    -- V_alt2(n + 1) expands to J(n, V_alt1(n))
    rw [V_alt2_succ_eval n]

    -- J(n, V_alt1(n))(0) evaluates to the full alternating sum of V_alt1(n)
    rw [J_zero_eq_SumA_for_V_sum_I n (V_alt1 n)]

    -- The alternating sum of V_alt1(n) equals the alternating sum of V_alt2(n)
    rw [SumA_V_alt1_eq_SumA_V_alt2 n]

    -- A value at an index (e.g., 0) is bounded above by the sequence's total sum
    have h := SumA_ge_eval_zero_for_V_sum_I n (V_alt2 n)

    -- Transitivity: 0 < V_alt2(n, 0) (from IH) <= SumA(n, V_alt2(n)) => 0 < SumA(n, V_alt2(n))
    exact Nat.lt_of_lt_of_le ih h

theorem I_zero_eq_zero_for_V_sum_I (n : ℕ) (A : Fin (n + 1) → ℕ) :
  I n A ⟨0, Nat.zero_lt_succ (n + 1)⟩ = 0 :=
by
  unfold I
  apply Finset.sum_eq_zero
  intro i _
  split_ifs with h
  · exfalso
    exact Nat.not_lt_zero _ h
  · rfl

theorem V_alt1_zero_for_V_sum_I {d : ℕ} (hd : 1 ≤ d) :
  V_alt1 d ⟨0, Nat.zero_lt_succ d⟩ = 0 :=
by
  cases d with
  | zero => omega
  | succ d' =>
    have h1 := I_zero_eq_zero_for_V_sum_I d' (V_alt2 d')
    have h2 := I_V_alt2_eq d' ⟨0, Nat.zero_lt_succ (d' + 1)⟩
    exact Eq.trans h2.symm h1

theorem I_one_eq_zero_eval_for_V_sum_I {d : ℕ} (A : Fin (d + 1) → ℕ) :
  I d A ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ d)⟩ = A ⟨0, Nat.zero_lt_succ d⟩ :=
by
  rw [I_eq_sum_filter]
  have H : Finset.filter (fun j : Fin (d + 1) => (j : ℕ) < ((⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ d)⟩ : Fin (d + 2)) : ℕ)) Finset.univ = {⟨0, Nat.zero_lt_succ d⟩} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro h
      apply Fin.ext
      -- Assign the hypothesis definitionally reducing the RHS bound to `1`
      have h1 : (x : ℕ) < 1 := h
      -- Derive that it must strictly be zero on the level of naturals
      have h2 : (x : ℕ) = 0 := by omega
      -- Use definitional equality `(⟨0, _⟩ : ℕ) ≡ 0` to close the `Fin.ext` goal
      exact h2
    · rintro rfl
      -- When `x = ⟨0, _⟩`, the required strict inequality is `0 < 1` which holds by `Nat.zero_lt_one`
      exact Nat.zero_lt_one
  rw [H, Finset.sum_singleton]

theorem sum_lt_sum_of_le_of_lt_A_for_V_sum_I {n : ℕ} (A B : Fin (n + 1) → ℕ)
  (hle : ∀ k, A k ≤ B k) (k₀ : Fin (n + 1)) (hlt : A k₀ < B k₀) :
  SumA n A < SumA n B :=
by
  rw [SumA_eq_sum n A, SumA_eq_sum n B]
  apply Finset.sum_lt_sum
  · intro i _
    exact hle i
  · exact ⟨k₀, Finset.mem_univ k₀, hlt⟩

theorem SumA_congr_for_V_sum_I {n : ℕ} (A B : Fin (n + 1) → ℕ) (h : ∀ k, A k = B k) :
  SumA n A = SumA n B :=
by
  have heq : A = B := funext h
  rw [heq]

theorem V_sum_lt_alt_step_I_alt1 {d : ℕ} (hd : 1 ≤ d) :
  SumA (d + 1) (I d (V_alt1 d)) < SumA (d + 1) (V_alt1 (d + 1)) :=
by
  have h2 : SumA (d + 1) (I d (V_alt2 d)) = SumA (d + 1) (V_alt1 (d + 1)) := by
    apply SumA_congr_for_V_sum_I
    intro k
    exact I_V_alt2_eq d k
  rw [← h2]
  refine sum_lt_sum_of_le_of_lt_A_for_V_sum_I (I d (V_alt1 d)) (I d (V_alt2 d)) (I_V_alt1_le_I_V_alt2 d) ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ d)⟩ ?_
  have eq1 : I d (V_alt1 d) ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ d)⟩ = V_alt1 d ⟨0, Nat.zero_lt_succ d⟩ := I_one_eq_zero_eval_for_V_sum_I (V_alt1 d)
  have eq2 : I d (V_alt2 d) ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ d)⟩ = V_alt2 d ⟨0, Nat.zero_lt_succ d⟩ := I_one_eq_zero_eval_for_V_sum_I (V_alt2 d)
  rw [eq1, eq2]
  have hz1 : V_alt1 d ⟨0, Nat.zero_lt_succ d⟩ = 0 := V_alt1_zero_for_V_sum_I hd
  have hz2 : 0 < V_alt2 d ⟨0, Nat.zero_lt_succ d⟩ := V_alt2_zero_pos_for_V_sum_I d
  rw [hz1]
  exact hz2

theorem SumA_J_V_alt2_eq_SumA_I_V_alt1 (d : ℕ) :
  SumA (d + 1) (J d (V_alt2 d)) = SumA (d + 1) (I d (V_alt1 d)) :=
by
  have h1 : ∀ k : Fin (d + 2), J d (V_alt2 d) k = I d (V_alt1 d) (k.rev) := by
    intro k
    exact J_eq_I_rev d (V_alt2 d) (V_alt1 d) (V_alt2_eq_rev d) k
  have h2 : SumA (d + 1) (J d (V_alt2 d)) = SumA (d + 1) (fun k => I d (V_alt1 d) (k.rev)) :=
    SumA_congr_for_V_sum_I (J d (V_alt2 d)) (fun k => I d (V_alt1 d) (k.rev)) h1
  rw [h2]
  exact SumA_rev_eq (d + 1) (I d (V_alt1 d))

theorem V_sum_lt_alt_step_J_alt2 {d : ℕ} (hd : 1 ≤ d) :
  SumA (d + 1) (J d (V_alt2 d)) < SumA (d + 1) (V_alt1 (d + 1)) :=
by
  rw [SumA_J_V_alt2_eq_SumA_I_V_alt1 d]
  exact V_sum_lt_alt_step_I_alt1 hd

theorem V_sum_lt_alt_step (d : ℕ) (hd : 1 ≤ d)
  (IH : ∀ s : Fin d → ℤˣ, s ≠ alt1_seq d → s ≠ alt2_seq d → SumA d (V d s) < SumA d (V_alt1 d))
  (s : Fin (d + 1) → ℤˣ) (h1 : s ≠ alt1_seq (d + 1)) (h2 : s ≠ alt2_seq (d + 1)) :
  SumA (d + 1) (V (d + 1) s) < SumA (d + 1) (V_alt1 (d + 1)) :=
by
  let s_prev : Fin d → ℤˣ := fun i => s (Fin.castSucc i)
  have h_bound : (∀ k, V d s_prev k ≤ V_alt1 d k) ∨ (∀ k, V d s_prev k ≤ V_alt2 d k) :=
    V_le_alt d s_prev
  by_cases h_last : s (Fin.last d) = (1 : ℤˣ)
  · have h_V : V (d + 1) s = I d (V d s_prev) := by
      funext k
      exact V_succ_eq_I d s h_last k
    rw [h_V]
    by_cases h_prev1 : s_prev = alt1_seq d
    · have h_V_prev : V d s_prev = V_alt1 d := by
        rw [h_prev1]
        exact V_eq_alt1 d
      rw [h_V_prev]
      exact V_sum_lt_alt_step_I_alt1 hd
    · by_cases h_prev2 : s_prev = alt2_seq d
      · have hs_eq : s = alt1_seq (d + 1) :=
          s_eq_alt1_of_prev_eq_alt2_and_last_eq_one s h_prev2 h_last
        exact (h1 hs_eq).elim
      · have h_lt : SumA d (V d s_prev) < SumA d (V_alt1 d) :=
          IH s_prev h_prev1 h_prev2
        exact V_sum_lt_alt_step_I_valid d (V d s_prev) h_bound h_lt
  · have h_last_neg : s (Fin.last d) = (-1 : ℤˣ) :=
      units_int_ne_one_implies_eq_neg_one (s (Fin.last d)) h_last
    have h_V : V (d + 1) s = J d (V d s_prev) := by
      funext k
      exact V_succ_eq_J d s h_last k
    rw [h_V]
    by_cases h_prev2 : s_prev = alt2_seq d
    · have h_V_prev : V d s_prev = V_alt2 d := by
        rw [h_prev2]
        exact V_eq_alt2 d
      rw [h_V_prev]
      exact V_sum_lt_alt_step_J_alt2 hd
    · by_cases h_prev1 : s_prev = alt1_seq d
      · have hs_eq : s = alt2_seq (d + 1) :=
          s_eq_alt2_of_prev_eq_alt1_and_last_eq_neg_one s h_prev1 h_last_neg
        exact (h2 hs_eq).elim
      · have h_lt : SumA d (V d s_prev) < SumA d (V_alt1 d) :=
          IH s_prev h_prev1 h_prev2
        exact V_sum_lt_alt_step_J_valid d (V d s_prev) h_bound h_lt

theorem V_sum_lt_alt (n : ℕ) (hn : 1 ≤ n) (s : Fin n → ℤˣ) :
  s ≠ alt1_seq n → s ≠ alt2_seq n → SumA n (V n s) < SumA n (V_alt1 n) :=
by
  revert hn s
  induction n with
  | zero =>
    intro hn s h1 h2
    omega
  | succ d IH =>
    intro hn s h1 h2
    have h_d_em : d = 0 ∨ d ≠ 0 := Classical.em _
    cases h_d_em with
    | inl hd =>
      rcases hd with rfl
      exact V_sum_lt_alt_base s h1 h2
    | inr hd =>
      have hd_pos : 1 ≤ d := by omega
      exact V_sum_lt_alt_step d hd_pos (IH hd_pos) s h1 h2

theorem f_eq_card_validPerms (n : ℕ) (s : Fin n → ℤˣ) :
  f n s = (Finset.filter (fun σ : Equiv.Perm (Fin (n + 1)) => ∀ i : Fin n, (0 : ℤ) < (s i : ℤ) * ((σ i.succ : ℤ) - (σ i.castSucc : ℤ))) Finset.univ).card :=
rfl

theorem mem_validPermsEnd_iff (n : ℕ) (s : Fin n → ℤˣ) (k : Fin (n + 1)) (σ : Equiv.Perm (Fin (n + 1))) :
  σ ∈ ValidPermsEnd n s k ↔
    (∀ i : Fin n, (0 : ℤ) < (s i : ℤ) * ((σ i.succ : ℤ) - (σ i.castSucc : ℤ))) ∧
    σ (Fin.last n) = k :=
by
  -- Unfold the definition of the set of valid permutations
  unfold ValidPermsEnd

  -- Simplify the membership condition of a filtered universal Finset
  -- `σ ∈ Finset.filter p Finset.univ` becomes `True ∧ p σ`, which reduces to `p σ`
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

  -- The simplified goal precisely matches the definition but with the logical AND clauses reversed
  exact and_comm

theorem validPermsEnd_card_eq_filter_card (n : ℕ) (s : Fin n → ℤˣ) (k : Fin (n + 1)) :
  (ValidPermsEnd n s k).card = (Finset.filter (fun a : Equiv.Perm (Fin (n + 1)) => (fun σ : Equiv.Perm (Fin (n + 1)) => σ (Fin.last n)) a = k)
    (Finset.filter (fun σ : Equiv.Perm (Fin (n + 1)) => ∀ i : Fin n, (0 : ℤ) < (s i : ℤ) * ((σ i.succ : ℤ) - (σ i.castSucc : ℤ))) Finset.univ)).card :=
by
  congr 1
  ext σ
  simp [mem_validPermsEnd_iff]

theorem f_eq_sum_DP (n : ℕ) (s : Fin n → ℤˣ) : f n s = ∑ k : Fin (n + 1), (ValidPermsEnd n s k).card :=
by
  rw [f_eq_card_validPerms]
  have h := Finset.card_eq_sum_card_fiberwise
    (f := fun σ : Equiv.Perm (Fin (n + 1)) => σ (Fin.last n))
    (s := Finset.filter (fun σ : Equiv.Perm (Fin (n + 1)) => ∀ i : Fin n, (0 : ℤ) < (s i : ℤ) * ((σ i.succ : ℤ) - (σ i.castSucc : ℤ))) Finset.univ)
    (t := (Finset.univ : Finset (Fin (n + 1))))
    (fun x _ => Finset.mem_univ ((fun σ : Equiv.Perm (Fin (n + 1)) => σ (Fin.last n)) x))
  rw [h]
  refine Finset.sum_congr rfl ?_
  intro k _
  exact (validPermsEnd_card_eq_filter_card n s k).symm

theorem ValidPermsEnd_mem {n : ℕ} (s : Fin n → ℤˣ) (k : Fin (n+1)) (σ : Equiv.Perm (Fin (n+1))) :
  σ ∈ ValidPermsEnd n s k ↔ σ (Fin.last n) = k ∧ ∀ i : Fin n, (0 : ℤ) < (s i : ℤ) * ((σ i.succ : ℤ) - (σ i.castSucc : ℤ)) :=
by
  simp only [ValidPermsEnd, Finset.mem_filter, Finset.mem_univ, true_and]

theorem sigma_castSucc_ne_k {n : ℕ} (k : Fin (n+2)) (σ : Equiv.Perm (Fin (n+2)))
  (h : σ (Fin.last (n+1)) = k) (i : Fin (n+1)) : σ (Fin.castSucc i) ≠ k :=
by
  intro hc
  have h_eq : σ (Fin.castSucc i) = σ (Fin.last (n+1)) := Eq.trans hc (Eq.symm h)
  have h_inj : Fin.castSucc i = Fin.last (n+1) := Equiv.injective σ h_eq
  exact Fin.castSucc_ne_last i h_inj

theorem exists_succAbove_eq {n : ℕ} (k x : Fin (n+2)) (hx : x ≠ k) :
  ∃ y : Fin (n+1), Fin.succAbove k y = x :=
by
  have h : x ∈ Set.range (Fin.succAbove k) := by
    -- Fin.range_succAbove states that the range of succAbove k is everything except k
    rw [Fin.range_succAbove]
    -- x ∈ {k}ᶜ is definitionally equivalent to ¬(x = k), which is our hypothesis `hx`
    exact hx
  -- x ∈ Set.range (Fin.succAbove k) is definitionally equivalent to ∃ y, Fin.succAbove k y = x
  exact h

theorem unextend_fun_exists_all {n : ℕ} (k : Fin (n+2)) (σ : Equiv.Perm (Fin (n+2)))
  (h : σ (Fin.last (n+1)) = k) :
  ∃ f : Fin (n+1) → Fin (n+1), ∀ i : Fin (n+1), Fin.succAbove k (f i) = σ (Fin.castSucc i) :=
by
  use fun i => Classical.choose (exists_succAbove_eq k (σ (Fin.castSucc i)) (sigma_castSucc_ne_k k σ h i))
  intro i
  exact Classical.choose_spec (exists_succAbove_eq k (σ (Fin.castSucc i)) (sigma_castSucc_ne_k k σ h i))

theorem unextend_fun_bijective {n : ℕ} (k : Fin (n+2)) (σ : Equiv.Perm (Fin (n+2)))
  (h : σ (Fin.last (n+1)) = k) (f : Fin (n+1) → Fin (n+1))
  (hf : ∀ i : Fin (n+1), Fin.succAbove k (f i) = σ (Fin.castSucc i)) : Function.Bijective f :=
by
  -- Since the domain and codomain are the same finite set, bijectivity is equivalent to injectivity
  apply Finite.injective_iff_bijective.mp
  intro x y hxy

  -- From f(x) = f(y), we apply Fin.succAbove k on both sides to show that σ(Fin.castSucc x) = σ(Fin.castSucc y)
  have h2 : σ (Fin.castSucc x) = σ (Fin.castSucc y) := by
    rw [← hf x, ← hf y, hxy]

  -- Since σ is a permutation (hence an equivalence), it is injective
  have h3 : Fin.castSucc x = Fin.castSucc y := Equiv.injective σ h2

  -- The function Fin.castSucc preserves the exact integer value of the element, hence x = y
  exact Fin.ext (congrArg (fun a => a.val) h3)

theorem exists_unextendPerm_apply {n : ℕ} (k : Fin (n+2)) (σ : Equiv.Perm (Fin (n+2)))
  (h : σ (Fin.last (n+1)) = k) :
  ∃ τ : Equiv.Perm (Fin (n+1)), ∀ i : Fin (n+1), σ (Fin.castSucc i) = Fin.succAbove k (τ i) :=
by
  obtain ⟨f, hf⟩ := unextend_fun_exists_all k σ h
  have hbij := unextend_fun_bijective k σ h f hf
  use Equiv.ofBijective f hbij
  intro i
  exact (hf i).symm

theorem extendFun_castSucc {n : ℕ} (k : Fin (n+2)) (τ : Equiv.Perm (Fin (n+1))) (i : Fin (n+1)) :
  extendFun k τ (Fin.castSucc i) = Fin.succAbove k (τ i) :=
by
  unfold extendFun
  simp

theorem my_succAbove_neq {m : ℕ} (k : Fin (m + 1)) (i : Fin m) : Fin.succAbove k i ≠ k :=
Fin.succAbove_ne k i

theorem extendFun_last {n : ℕ} (k : Fin (n+2)) (τ : Equiv.Perm (Fin (n+1))) :
  extendFun k τ (Fin.last (n+1)) = k :=
by
  simp [extendFun]

theorem succAbove_inj_lem {n : ℕ} (k : Fin (n+2)) {x y : Fin (n+1)} :
  Fin.succAbove k x = Fin.succAbove k y → x = y :=
by
  intro h
  exact Fin.succAbove_right_inj.mp h

theorem perm_inj_lem {n : ℕ} (τ : Equiv.Perm (Fin (n+1))) {x y : Fin (n+1)} :
  τ x = τ y → x = y :=
fun h => (Equiv.apply_eq_iff_eq τ).mp h

theorem extendFun_injective {n : ℕ} (k : Fin (n+2)) (τ : Equiv.Perm (Fin (n+1))) :
  Function.Injective (extendFun k τ) :=
by
  intro x y hxy
  revert hxy
  revert y
  revert x
  apply Fin.lastCases
  · apply Fin.lastCases
    · intro h
      rfl
    · intro j h
      rw [extendFun_last, extendFun_castSucc] at h
      have contra := my_succAbove_neq k (τ j)
      exact False.elim (contra h.symm)
  · intro i
    apply Fin.lastCases
    · intro h
      rw [extendFun_castSucc, extendFun_last] at h
      have contra := my_succAbove_neq k (τ i)
      exact False.elim (contra h)
    · intro j h
      rw [extendFun_castSucc, extendFun_castSucc] at h
      have h_eq := succAbove_inj_lem k h
      have h_eq2 := perm_inj_lem τ h_eq
      rw [h_eq2]

theorem extendFun_bijective {n : ℕ} (k : Fin (n+2)) (τ : Equiv.Perm (Fin (n+1))) :
  Function.Bijective (extendFun k τ) :=
Finite.injective_iff_bijective.mp (extendFun_injective k τ)

theorem extendFun_exists_perm {n : ℕ} (k : Fin (n+2)) (τ : Equiv.Perm (Fin (n+1))) :
  ∃ σ : Equiv.Perm (Fin (n+2)), ∀ i, σ i = extendFun k τ i :=
⟨Equiv.ofBijective (extendFun k τ) (extendFun_bijective k τ), fun _ => rfl⟩

theorem extendPerm_spec {n : ℕ} (k : Fin (n+2)) (τ : Equiv.Perm (Fin (n+1))) (i : Fin (n+2)) :
  extendPerm k τ i = extendFun k τ i :=
Classical.epsilon_spec (extendFun_exists_perm k τ) i

theorem extendPerm_castSucc {n : ℕ} (k : Fin (n+2)) (τ : Equiv.Perm (Fin (n+1))) (i : Fin (n+1)) :
  extendPerm k τ (Fin.castSucc i) = Fin.succAbove k (τ i) :=
by
  rw [extendPerm_spec, extendFun_castSucc]

theorem extendPerm_last {n : ℕ} (k : Fin (n+2)) (τ : Equiv.Perm (Fin (n+1))) :
  extendPerm k τ (Fin.last (n+1)) = k :=
by
  let e : Equiv.Perm (Fin (n+2)) := extendPerm k τ
  have h_cast : ∀ i : Fin (n+1), e (Fin.castSucc i) ≠ k := by
    intro i h
    have h1 : e (Fin.castSucc i) = Fin.succAbove k (τ i) := extendPerm_castSucc k τ i
    rw [h1] at h
    exact my_succAbove_neq k (τ i) h
  have h_ex : ∃ x, e x = k := ⟨e.symm k, Equiv.apply_symm_apply e k⟩
  change e (Fin.last (n+1)) = k
  apply Exists.elim h_ex
  intro x hx
  revert hx
  refine Fin.lastCases ?_ ?_ x
  · intro h
    exact h
  · intro i h
    exact False.elim (h_cast i h)

theorem extendPerm_of_apply {n : ℕ} (k : Fin (n+2)) (τ : Equiv.Perm (Fin (n+1))) (σ : Equiv.Perm (Fin (n+2)))
  (h_last : σ (Fin.last (n+1)) = k)
  (h_apply : ∀ i : Fin (n+1), σ (Fin.castSucc i) = Fin.succAbove k (τ i)) :
  extendPerm k τ = σ :=
by
  apply Equiv.ext
  intro x
  refine Fin.lastCases ?_ ?_ x
  · rw [extendPerm_last k τ, h_last]
  · intro i
    rw [extendPerm_castSucc k τ i, h_apply i]

theorem exists_extendPerm {n : ℕ} (k : Fin (n+2)) (σ : Equiv.Perm (Fin (n+2)))
  (h : σ (Fin.last (n+1)) = k) : ∃ τ : Equiv.Perm (Fin (n+1)), extendPerm k τ = σ :=
by
  obtain ⟨τ, hτ⟩ := exists_unextendPerm_apply k σ h
  exact ⟨τ, extendPerm_of_apply k τ σ h hτ⟩

theorem succ_last {n : ℕ} : (Fin.last n).succ = Fin.last (n+1) :=
rfl

theorem succAbove_val_lt_iff {n : ℕ} (p : Fin (n+2)) (i : Fin (n+1)) :
  (Fin.succAbove p i).val < p.val ↔ i.val < p.val :=
by
  exact Fin.succAbove_lt_iff_castSucc_lt p i

theorem extendPerm_cond_last_helper {n : ℕ} (k x : Fin (n+2)) :
  (0 : ℤ) < ((1 : ℤˣ) : ℤ) * ((k : ℤ) - (x : ℤ)) ↔ x.val < k.val :=
by
  change (0 : ℤ) < 1 * ((k : ℤ) - (x : ℤ)) ↔ x.val < k.val
  rw [one_mul]
  omega

theorem extendPerm_cond_last {n : ℕ} (k : Fin (n+2)) (τ : Equiv.Perm (Fin (n+1))) :
  (0 : ℤ) < ((1 : ℤˣ) : ℤ) * ((extendPerm k τ (Fin.last (n+1)) : ℤ) - (extendPerm k τ (Fin.last n).castSucc : ℤ)) ↔
  (τ (Fin.last n)).val < k.val :=
by
  have h1 : extendPerm k τ (Fin.last (n+1)) = k := extendPerm_last k τ
  have h2 : extendPerm k τ (Fin.last n).castSucc = Fin.succAbove k (τ (Fin.last n)) := extendPerm_castSucc k τ (Fin.last n)
  rw [h1, h2]
  exact Iff.trans (extendPerm_cond_last_helper k (Fin.succAbove k (τ (Fin.last n)))) (succAbove_val_lt_iff k (τ (Fin.last n)))

theorem castSucc_succ_eq_succ_castSucc {n : ℕ} (j : Fin n) :
  Fin.succ (Fin.castSucc j) = Fin.castSucc (Fin.succ j) :=
rfl

theorem extendPerm_castSucc_succ_eq {n : ℕ} (k : Fin (n+2)) (τ : Equiv.Perm (Fin (n+1))) (i : Fin n) :
  extendPerm k τ (Fin.castSucc i).succ = Fin.succAbove k (τ i.succ) :=
by
  rw [castSucc_succ_eq_succ_castSucc]
  rw [extendPerm_castSucc]

theorem extendPerm_castSucc_castSucc_eq {n : ℕ} (k : Fin (n+2)) (τ : Equiv.Perm (Fin (n+1))) (i : Fin n) :
  extendPerm k τ (Fin.castSucc i).castSucc = Fin.succAbove k (τ i.castSucc) :=
by
  exact extendPerm_castSucc k τ (Fin.castSucc i)

theorem Int_units_val_eq_one_or_neg_one (u : ℤˣ) : (u : ℤ) = 1 ∨ (u : ℤ) = -1 :=
by
  rcases Int.units_eq_one_or u with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem Fin_succAbove_lt_iff {n : ℕ} (k : Fin (n+2)) (x y : Fin (n+1)) :
  (Fin.succAbove k x : ℤ) < (Fin.succAbove k y : ℤ) ↔ (x : ℤ) < (y : ℤ) :=
by
  have h : Fin.succAbove k x < Fin.succAbove k y ↔ x < y :=
    (Fin.strictMono_succAbove k).lt_iff_lt
  constructor
  · intro h1
    have h2 : Fin.succAbove k x < Fin.succAbove k y := by omega
    have h3 : x < y := h.mp h2
    omega
  · intro h1
    have h2 : x < y := by omega
    have h3 : Fin.succAbove k x < Fin.succAbove k y := h.mpr h2
    omega

theorem Int_units_mul_succAbove_sub_pos_iff {n : ℕ} (k : Fin (n+2)) (x y : Fin (n+1)) (u : ℤˣ) :
  (0 : ℤ) < (u : ℤ) * ((Fin.succAbove k y : ℤ) - (Fin.succAbove k x : ℤ)) ↔
  (0 : ℤ) < (u : ℤ) * ((y : ℤ) - (x : ℤ)) :=
by
  have hu := Int_units_val_eq_one_or_neg_one u
  have h1 := Fin_succAbove_lt_iff k x y
  have h2 := Fin_succAbove_lt_iff k y x
  rcases hu with h_one | h_neg_one
  · rw [h_one]
    constructor
    · intro h
      have h_lt : (Fin.succAbove k x : ℤ) < (Fin.succAbove k y : ℤ) := by omega
      have h_lt2 : (x : ℤ) < (y : ℤ) := h1.mp h_lt
      omega
    · intro h
      have h_lt : (x : ℤ) < (y : ℤ) := by omega
      have h_lt2 : (Fin.succAbove k x : ℤ) < (Fin.succAbove k y : ℤ) := h1.mpr h_lt
      omega
  · rw [h_neg_one]
    constructor
    · intro h
      have h_lt : (Fin.succAbove k y : ℤ) < (Fin.succAbove k x : ℤ) := by omega
      have h_lt2 : (y : ℤ) < (x : ℤ) := h2.mp h_lt
      omega
    · intro h
      have h_lt : (y : ℤ) < (x : ℤ) := by omega
      have h_lt2 : (Fin.succAbove k y : ℤ) < (Fin.succAbove k x : ℤ) := h2.mpr h_lt
      omega

theorem extendPerm_cond_castSucc {n : ℕ} (k : Fin (n+2)) (τ : Equiv.Perm (Fin (n+1))) (s : Fin (n+1) → ℤˣ) (i : Fin n) :
  (0 : ℤ) < (s (Fin.castSucc i) : ℤ) * ((extendPerm k τ (Fin.castSucc i).succ : ℤ) - (extendPerm k τ (Fin.castSucc i).castSucc : ℤ)) ↔
  (0 : ℤ) < (s (Fin.castSucc i) : ℤ) * ((τ i.succ : ℤ) - (τ i.castSucc : ℤ)) :=
by
  rw [extendPerm_castSucc_succ_eq, extendPerm_castSucc_castSucc_eq, Int_units_mul_succAbove_sub_pos_iff]

theorem extendPerm_satisfies_cond {n : ℕ} (k : Fin (n+2)) (τ : Equiv.Perm (Fin (n+1))) (s : Fin (n+1) → ℤˣ)
  (h_last : s (Fin.last n) = (1 : ℤˣ))
  (h_j : (τ (Fin.last n)).val < k.val)
  (h_τ : ∀ i : Fin n, (0 : ℤ) < (s (Fin.castSucc i) : ℤ) * ((τ i.succ : ℤ) - (τ i.castSucc : ℤ))) :
  ∀ i : Fin (n+1), (0 : ℤ) < (s i : ℤ) * ((extendPerm k τ i.succ : ℤ) - (extendPerm k τ i.castSucc : ℤ)) :=
by
  intro i
  -- Proceed by case analysis structurally using `Fin.lastCases`
  refine Fin.lastCases ?_ ?_ i
  · -- Case 1: `i = Fin.last n`
    rw [h_last, succ_last, extendPerm_cond_last]
    exact h_j
  · -- Case 2: `i = Fin.castSucc j` for some `j : Fin n`
    intro j
    rw [extendPerm_cond_castSucc]
    exact h_τ j

theorem ValidPermsEnd_succ_eq_image_I {n : ℕ} (s : Fin (n+1) → ℤˣ) (k : Fin (n+2))
  (h : s (Fin.last n) = (1 : ℤˣ)) :
  ValidPermsEnd (n+1) s k =
    (Finset.filter (fun (j : Fin (n+1)) => j.val < k.val) Finset.univ).biUnion
      (fun j => (ValidPermsEnd n (fun i => s (Fin.castSucc i)) j).image (extendPerm k)) :=
by
  ext σ
  simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · intro hσ
    rw [ValidPermsEnd_mem] at hσ
    rcases hσ with ⟨h_last, h_cond⟩
    have ⟨τ, hτ_eq⟩ := exists_extendPerm k σ h_last
    use τ (Fin.last n)
    constructor
    · have h_last_n := h_cond (Fin.last n)
      rw [← hτ_eq] at h_last_n
      rw [h, succ_last] at h_last_n
      rwa [extendPerm_cond_last] at h_last_n
    · use τ
      constructor
      · rw [ValidPermsEnd_mem]
        constructor
        · rfl
        · intro i
          have h_i := h_cond (Fin.castSucc i)
          rw [← hτ_eq] at h_i
          rwa [extendPerm_cond_castSucc] at h_i
      · exact hτ_eq
  · rintro ⟨j, hj, τ, hτ, hτ_eq⟩
    rw [ValidPermsEnd_mem] at hτ
    rcases hτ with ⟨hτ_last, hτ_cond⟩
    rw [ValidPermsEnd_mem]
    constructor
    · rw [← hτ_eq]
      exact extendPerm_last k τ
    · have hj_τ : (τ (Fin.last n)).val < k.val := by
        rw [hτ_last]
        exact hj
      rw [← hτ_eq]
      exact extendPerm_satisfies_cond k τ s h hj_τ hτ_cond

theorem mem_ValidPermsEnd {n : ℕ} (s : Fin n → ℤˣ) (k : Fin (n + 1)) (σ : Equiv.Perm (Fin (n + 1))) :
  σ ∈ ValidPermsEnd n s k ↔
  σ (Fin.last n) = k ∧ ∀ i : Fin n, (0 : ℤ) < (s i : ℤ) * ((σ i.succ : ℤ) - (σ i.castSucc : ℤ)) :=
by
  simp only [ValidPermsEnd, Finset.mem_filter, Finset.mem_univ, true_and]

theorem s_last_eq_neg_one {n : ℕ} (s : Fin (n+1) → ℤˣ) (h : s (Fin.last n) ≠ (1 : ℤˣ)) :
  s (Fin.last n) = (-1 : ℤˣ) :=
by
  have H := Int.units_eq_one_or (s (Fin.last n))
  cases H with
  | inl h1 => exact False.elim (h h1)
  | inr h2 => exact h2

theorem extendPerm_cond_last_neg_helper {n : ℕ} (k x : Fin (n+2)) :
  (0 : ℤ) < ((-1 : ℤˣ) : ℤ) * ((k : ℤ) - (x : ℤ)) ↔ k.val < x.val :=
by
  have h : ((-1 : ℤˣ) : ℤ) = -1 := rfl
  rw [h]
  omega

theorem succAbove_val_gt_iff {n : ℕ} (p : Fin (n+2)) (i : Fin (n+1)) :
  p.val < (Fin.succAbove p i).val ↔ p.val ≤ i.val :=
by
  have h1 := succAbove_val_lt_iff p i
  have h2 := my_succAbove_neq p i
  have h3 : (Fin.succAbove p i).val ≠ p.val := fun h => h2 (Fin.ext h)
  omega

theorem extendPerm_cond_last_neg {n : ℕ} (k : Fin (n+2)) (τ : Equiv.Perm (Fin (n+1))) :
  (0 : ℤ) < ((-1 : ℤˣ) : ℤ) * ((extendPerm k τ (Fin.last (n+1)) : ℤ) - (extendPerm k τ (Fin.last n).castSucc : ℤ)) ↔
  k.val ≤ (τ (Fin.last n)).val :=
by
  rw [extendPerm_last k τ, extendPerm_castSucc k τ (Fin.last n)]
  rw [extendPerm_cond_last_neg_helper k (Fin.succAbove k (τ (Fin.last n)))]
  rw [succAbove_val_gt_iff k (τ (Fin.last n))]

theorem Fin_cases_last {n : ℕ} {p : Fin (n+1) → Prop}
  (h_cast : ∀ i : Fin n, p (Fin.castSucc i))
  (h_last : p (Fin.last n)) :
  ∀ x : Fin (n+1), p x :=
Fin.forall_iff_castSucc.mpr ⟨h_last, h_cast⟩

theorem valid_extendPerm_iff {n : ℕ} (s : Fin (n+1) → ℤˣ) (k : Fin (n+2)) (τ : Equiv.Perm (Fin (n+1)))
  (h_s_last : s (Fin.last n) = (-1 : ℤˣ)) :
  (∀ x : Fin (n+1), (0 : ℤ) < (s x : ℤ) * ((extendPerm k τ x.succ : ℤ) - (extendPerm k τ x.castSucc : ℤ))) ↔
  ((∀ i : Fin n, (0 : ℤ) < (s (Fin.castSucc i) : ℤ) * ((τ i.succ : ℤ) - (τ i.castSucc : ℤ))) ∧
   k.val ≤ (τ (Fin.last n)).val) :=
by
  constructor
  · intro h
    constructor
    · intro i
      rw [← extendPerm_cond_castSucc k τ s i]
      exact h (Fin.castSucc i)
    · have h1 := h (Fin.last n)
      rw [h_s_last, succ_last] at h1
      rw [← extendPerm_cond_last_neg k τ]
      exact h1
  · intro h
    have h_cast := h.1
    have h_last := h.2
    apply Fin_cases_last
    · intro i
      rw [extendPerm_cond_castSucc k τ s i]
      exact h_cast i
    · rw [h_s_last, succ_last]
      rw [extendPerm_cond_last_neg k τ]
      exact h_last

theorem exists_extendPerm_iff {n : ℕ} (k : Fin (n+2)) (σ : Equiv.Perm (Fin (n+2))) :
  (∃ τ : Equiv.Perm (Fin (n+1)), extendPerm k τ = σ) ↔ σ (Fin.last (n+1)) = k :=
by
  constructor
  · rintro ⟨τ, rfl⟩
    exact extendPerm_last k τ
  · intro h
    exact exists_extendPerm k σ h

theorem ValidPermsEnd_succ_eq_image_J {n : ℕ} (s : Fin (n+1) → ℤˣ) (k : Fin (n+2))
  (h : s (Fin.last n) ≠ (1 : ℤˣ)) :
  ValidPermsEnd (n+1) s k =
    (Finset.filter (fun (j : Fin (n+1)) => k.val ≤ j.val) Finset.univ).biUnion
      (fun j => (ValidPermsEnd n (fun i => s (Fin.castSucc i)) j).image (extendPerm k)) :=
by
  ext σ
  simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and, and_true]
  rw [mem_ValidPermsEnd]
  constructor
  · rintro ⟨h_last, h_valid⟩
    have h_s_last : s (Fin.last n) = (-1 : ℤˣ) := s_last_eq_neg_one s h
    have h_exists : ∃ τ : Equiv.Perm (Fin (n+1)), extendPerm k τ = σ := (exists_extendPerm_iff k σ).mpr h_last
    rcases h_exists with ⟨τ, hτ_eq⟩
    subst hτ_eq
    rw [valid_extendPerm_iff s k τ h_s_last] at h_valid
    use τ (Fin.last n)
    refine ⟨h_valid.2, τ, ?_, rfl⟩
    rw [mem_ValidPermsEnd]
    exact ⟨rfl, h_valid.1⟩
  · rintro ⟨j, hj, τ, hτ, rfl⟩
    rw [mem_ValidPermsEnd] at hτ
    constructor
    · exact extendPerm_last k τ
    · have h_s_last : s (Fin.last n) = (-1 : ℤˣ) := s_last_eq_neg_one s h
      rw [valid_extendPerm_iff s k τ h_s_last]
      refine ⟨hτ.2, ?_⟩
      rw [hτ.1]
      exact hj

theorem image_extendPerm_disjoint {n : ℕ} (s : Fin n → ℤˣ) (k : Fin (n+2)) {j1 j2 : Fin (n+1)} (hj : j1 ≠ j2) :
  Disjoint ((ValidPermsEnd n s j1).image (extendPerm k)) ((ValidPermsEnd n s j2).image (extendPerm k)) :=
by
  -- Rewrite disjointness into a point-wise logic
  rw [Finset.disjoint_left]
  intro σ h1 h2

  -- Unfold the definition of image for both hypotheses
  rw [Finset.mem_image] at h1 h2

  -- Extract the base permutations τ₁ and τ₂ from the sets
  rcases h1 with ⟨τ1, hτ1, rfl⟩
  rcases h2 with ⟨τ2, hτ2, eq2⟩

  -- From their set membership, we know τ₁ and τ₂ end precisely at j₁ and j₂
  have hτ1_eq := ((ValidPermsEnd_mem s j1 τ1).mp hτ1).left
  have hτ2_eq := ((ValidPermsEnd_mem s j2 τ2).mp hτ2).left

  -- Evaluate both extended permutations at the casted last element
  have eq_castSucc : extendPerm k τ1 (Fin.castSucc (Fin.last n)) = extendPerm k τ2 (Fin.castSucc (Fin.last n)) := by
    rw [eq2]

  -- Rewrite these evaluations using the known simplification lemma
  rw [extendPerm_castSucc k τ1 (Fin.last n), extendPerm_castSucc k τ2 (Fin.last n)] at eq_castSucc

  -- Substitute the known ending evaluations (j₁ and j₂) into our equality
  rw [hτ1_eq, hτ2_eq] at eq_castSucc

  -- Apply the injectivity of `Fin.succAbove` to deduce j₁ = j₂
  -- This directly contradicts our hypothesis hj : j₁ ≠ j₂
  exact hj (Fin.succAbove_right_inj.mp eq_castSucc)

theorem extendPerm_injective {n : ℕ} (k : Fin (n+2)) :
  Function.Injective (extendPerm k) :=
by
  intro τ1 τ2 h
  -- Explicitly apply Equiv.ext to keep the goal at τ1 i = τ2 i instead of decomposing into Nat
  apply Equiv.ext
  intro i
  -- Evaluate the extended permutations at Fin.castSucc i
  have h_eval : extendPerm k τ1 (Fin.castSucc i) = extendPerm k τ2 (Fin.castSucc i) := by
    rw [h]
  -- Rewrite using the pre-established lemma for extendPerm
  rw [extendPerm_castSucc k τ1 i, extendPerm_castSucc k τ2 i] at h_eval
  -- Fin.succAbove_right_injective directly solves the equality τ1 i = τ2 i
  exact Fin.succAbove_right_injective h_eval

theorem card_image_extendPerm {n : ℕ} (k : Fin (n+2)) (s : Fin n → ℤˣ) (j : Fin (n+1)) :
  ((ValidPermsEnd n s j).image (extendPerm k)).card = (ValidPermsEnd n s j).card :=
Finset.card_image_of_injective (ValidPermsEnd n s j) (extendPerm_injective k)

theorem I_def {n : ℕ} (A : Fin (n+1) → ℕ) (k : Fin (n+2)) :
  I n A k = ∑ j ∈ Finset.filter (fun (j : Fin (n+1)) => j.val < k.val) Finset.univ, A j :=
by
  unfold I
  rw [Finset.sum_filter]

theorem sum_card_image_extendPerm_I {n : ℕ} (s : Fin n → ℤˣ) (k : Fin (n+2)) :
  ((Finset.filter (fun (j : Fin (n+1)) => j.val < k.val) Finset.univ).biUnion
      (fun j => (ValidPermsEnd n s j).image (extendPerm k))).card =
  I n (fun j => (ValidPermsEnd n s j).card) k :=
by
  have h_disj : Set.PairwiseDisjoint (Finset.filter (fun (j : Fin (n+1)) => j.val < k.val) Finset.univ : Set (Fin (n+1)))
    (fun j => (ValidPermsEnd n s j).image (extendPerm k)) := by
    intro x _ y _ hxy
    exact image_extendPerm_disjoint s k hxy
  rw [Finset.card_biUnion h_disj]
  rw [I_def]
  apply Finset.sum_congr rfl
  intro j _
  exact card_image_extendPerm k s j

theorem ValidPermsEnd_image_extendPerm_disjoint_J {n : ℕ} (s : Fin n → ℤˣ) (k : Fin (n+2)) :
  (↑(Finset.filter (fun (j : Fin (n+1)) => k.val ≤ j.val) Finset.univ) : Set (Fin (n+1))).PairwiseDisjoint
    (fun j => (ValidPermsEnd n s j).image (extendPerm k)) :=
by
  intro j1 hj1 j2 hj2 hj_neq
  dsimp only [Function.onFun]
  rw [Finset.disjoint_left]
  intro x hx1 hx2
  rw [Finset.mem_image] at hx1 hx2
  rcases hx1 with ⟨σ1, hσ1, eq1⟩
  rcases hx2 with ⟨σ2, hσ2, eq2⟩
  have H : extendPerm k σ1 = extendPerm k σ2 := by
    rw [eq1]
    exact eq2.symm
  have H1 : extendPerm k σ1 (Fin.castSucc (Fin.last n)) = extendPerm k σ2 (Fin.castSucc (Fin.last n)) :=
    congrArg (fun σ => σ (Fin.castSucc (Fin.last n))) H
  rw [extendPerm_castSucc k σ1 (Fin.last n), extendPerm_castSucc k σ2 (Fin.last n)] at H1
  have h_σ1_last : σ1 (Fin.last n) = j1 := by
    have := (mem_ValidPermsEnd s j1 σ1).mp hσ1
    exact this.1
  have h_σ2_last : σ2 (Fin.last n) = j2 := by
    have := (mem_ValidPermsEnd s j2 σ2).mp hσ2
    exact this.1
  rw [h_σ1_last, h_σ2_last] at H1
  have hj_eq : j1 = j2 := Fin.succAbove_right_injective H1
  exact hj_neq hj_eq

theorem J_def_J {n : ℕ} (A : Fin (n+1) → ℕ) (k : Fin (n+2)) :
  J n A k = ∑ j ∈ Finset.filter (fun (j : Fin (n+1)) => k.val ≤ j.val) Finset.univ, A j :=
by
  unfold J
  rw [Finset.sum_filter]

theorem card_image_extendPerm_J {n : ℕ} (s : Fin n → ℤˣ) (k : Fin (n+2)) (j : Fin (n+1)) :
  ((ValidPermsEnd n s j).image (extendPerm k)).card = (ValidPermsEnd n s j).card :=
by
  exact Finset.card_image_of_injective (ValidPermsEnd n s j) (extendPerm_injective k)

theorem sum_card_image_extendPerm_J {n : ℕ} (s : Fin n → ℤˣ) (k : Fin (n+2)) :
  ((Finset.filter (fun (j : Fin (n+1)) => k.val ≤ j.val) Finset.univ).biUnion
      (fun j => (ValidPermsEnd n s j).image (extendPerm k))).card =
  J n (fun j => (ValidPermsEnd n s j).card) k :=
by
  -- Convert the cardinality of the disjoint union of images into a sum of their cardinalities
  rw [Finset.card_biUnion (ValidPermsEnd_image_extendPerm_disjoint_J s k)]
  -- Unfold the sum definition of J
  rw [J_def_J]
  -- Show that the arguments inside both bounded sums correspond term-by-term
  apply Finset.sum_congr rfl
  intro j _
  -- Apply injectivity to simplify the cardinality of the individual image configurations
  rw [card_image_extendPerm_J]

theorem ValidPermsEnd_zero_eq_univ (s : Fin 0 → ℤˣ) (k : Fin 1) :
  ValidPermsEnd 0 s k = (Finset.univ : Finset (Equiv.Perm (Fin 1))) :=
by
  apply Finset.ext
  intro σ
  rw [ValidPermsEnd_mem]
  constructor
  · intro _
    exact Finset.mem_univ σ
  · intro _
    constructor
    · apply Fin.ext
      have h1 := (σ (Fin.last 0)).isLt
      have h2 := k.isLt
      omega
    · intro i
      exact Fin.elim0 i

theorem card_univ_Perm_Fin_one : (Finset.univ : Finset (Equiv.Perm (Fin 1))).card = 1 :=
by
  rw [Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
  rfl

theorem V_zero_eq_one (s : Fin 0 → ℤˣ) (k : Fin 1) : V 0 s k = 1 :=
rfl

theorem DP_eq_V_zero (s : Fin 0 → ℤˣ) (k : Fin 1) :
  (ValidPermsEnd 0 s k).card = V 0 s k :=
by
  rw [ValidPermsEnd_zero_eq_univ s k]
  rw [card_univ_Perm_Fin_one]
  rw [V_zero_eq_one s k]

theorem DP_eq_V (n : ℕ) (s : Fin n → ℤˣ) (k : Fin (n + 1)) : (ValidPermsEnd n s k).card = V n s k :=
by
  revert s k
  induction n with
  | zero =>
    intro s k
    exact DP_eq_V_zero s k
  | succ d ih =>
    intro s k
    by_cases h : s (Fin.last d) = (1 : ℤˣ)
    · rw [ValidPermsEnd_succ_eq_image_I s k h, sum_card_image_extendPerm_I (fun i => s (Fin.castSucc i)) k]
      have heq : (fun j => (ValidPermsEnd d (fun i => s (Fin.castSucc i)) j).card) = V d (fun i => s (Fin.castSucc i)) := by
        funext j
        exact ih (fun i => s (Fin.castSucc i)) j
      rw [heq, ← V_succ_eq_I d s h k]
    · rw [ValidPermsEnd_succ_eq_image_J s k h, sum_card_image_extendPerm_J (fun i => s (Fin.castSucc i)) k]
      have heq : (fun j => (ValidPermsEnd d (fun i => s (Fin.castSucc i)) j).card) = V d (fun i => s (Fin.castSucc i)) := by
        funext j
        exact ih (fun i => s (Fin.castSucc i)) j
      rw [heq, ← V_succ_eq_J d s h k]

theorem f_eq_SumA (n : ℕ) (s : Fin n → ℤˣ) : f n s = SumA n (V n s) :=
by
  have h1 : f n s = ∑ k : Fin (n + 1), V n s k := by
    rw [f_eq_sum_DP]
    apply Finset.sum_congr rfl
    intro x _
    exact DP_eq_V n s x
  exact h1

theorem putnam_2025_a5 (n : ℕ)
    (hn : 1 ≤ n)
    (s : Fin n → ℤˣ) : (∀ t : Fin n → ℤˣ, f n t ≤ f n s) ↔ s ∈ putnam_2025_a5_solution n :=
by
  constructor
  · intro H
    by_contra h_not_in
    have h_not_alt1 : s ≠ alt1_seq n := by
      intro h_eq
      apply h_not_in
      rw [solution_iff n hn]
      left
      exact h_eq
    have h_not_alt2 : s ≠ alt2_seq n := by
      intro h_eq
      apply h_not_in
      rw [solution_iff n hn]
      right
      exact h_eq
    have h_lt : SumA n (V n s) < SumA n (V_alt1 n) := V_sum_lt_alt n hn s h_not_alt1 h_not_alt2
    have h_f_s : f n s = SumA n (V n s) := f_eq_SumA n s
    have h_f_t : f n (alt1_seq n) = SumA n (V_alt1 n) := by
      rw [f_eq_SumA n (alt1_seq n)]
      rw [V_eq_alt1 n]
    have h_le : f n (alt1_seq n) ≤ f n s := H (alt1_seq n)
    omega
  · intro H t
    have h_s_eq : s = alt1_seq n ∨ s = alt2_seq n := (solution_iff n hn s).mp H
    have h_f_s : f n s = SumA n (V_alt1 n) := by
      cases h_s_eq with
      | inl h1 =>
        rw [h1, f_eq_SumA n (alt1_seq n), V_eq_alt1 n]
      | inr h2 =>
        rw [h2, f_eq_SumA n (alt2_seq n), V_eq_alt2 n, ← SumA_V_alt1_eq_SumA_V_alt2 n]
    have h_f_t : f n t = SumA n (V n t) := f_eq_SumA n t
    rw [h_f_s, h_f_t]
    have h_le_alt := V_le_alt n t
    cases h_le_alt with
    | inl h_le1 =>
      exact SumA_mono h_le1
    | inr h_le2 =>
      calc SumA n (V n t) ≤ SumA n (V_alt2 n) := SumA_mono h_le2
        _ = SumA n (V_alt1 n) := (SumA_V_alt1_eq_SumA_V_alt2 n).symm
