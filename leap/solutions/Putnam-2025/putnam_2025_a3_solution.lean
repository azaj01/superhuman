import Mathlib
open Finset
open Function
abbrev putnam_2025_a3_solution : ℕ → Bool := fun _ => false
abbrev GameString (n : ℕ) := Fin n → Fin 3
abbrev initialState (n : ℕ) : GameString n := fun _ => 0
abbrev isValidMove {n : ℕ} (s1 s2 : GameString n) : Prop :=
  (∃! i : Fin n, s1 i ≠ s2 i) ∧
  ∀ i : Fin n, s1 i ≠ s2 i →
    ((s1 i).val + 1 = (s2 i).val ∨ (s2 i).val + 1 = (s1 i).val)
abbrev IsValidGamePlay {n : ℕ} (play : List (GameString n)) : Prop :=
  play.Chain isValidMove (initialState n) ∧
  (initialState n :: play).Nodup
inductive HasWinningStrategy (n : ℕ) : List (GameString n) → Prop where
  | win (play : List (GameString n)) (s : GameString n) :
      IsValidGamePlay (play ++ [s]) →
      (∀ s', IsValidGamePlay (play ++ [s, s']) → HasWinningStrategy n (play ++ [s, s'])) →
      HasWinningStrategy n play
abbrev AliceHasWinningStrategy (n : ℕ) : Prop := HasWinningStrategy n []

def firstNonZero {n : ℕ} (x : GameString n) : Option (Fin n) :=
  let S := Finset.univ.filter (fun i => x i ≠ 0)
  if h : S.Nonempty then some (S.min' h) else none
def M {n : ℕ} (x : GameString n) : GameString n :=
  match firstNonZero x with
  | none => x
  | some i => Function.update x i (if x i = 1 then 2 else 1)
inductive BobPairs {n : ℕ} : List (GameString n) → Prop
  | nil : BobPairs []
  | cons (s1 s2 : GameString n) (rest : List (GameString n)) :
      s2 = M s1 → BobPairs rest → BobPairs (s1 :: s2 :: rest)

theorem aux_chain_append_last {α : Type*} (R : α → α → Prop) (a : α) (L : List α) (x y : α)
  (h1 : List.Chain R a (L ++ [x])) (h2 : R x y) :
  List.Chain R a (L ++ [x, y]) :=
by
  induction L generalizing a with
  | nil =>
    -- Base Case (L = []): h1 proves the chain [x].
    -- We extract `R a x` and drop the empty tail.
    cases h1 with
    | cons_cons h_ax _ =>
      -- We piece it back together as `a → x → y → []`.
      constructor
      · exact h_ax
      · constructor
        · exact h2
        · constructor
  | cons hd tl ih =>
    -- Inductive Step (L = hd :: tl): L ++ [x] simplifies to hd :: (tl ++ [x]).
    -- h1 proves the chain `a → hd → ... → x`. We extract the head link and the tail chain.
    cases h1 with
    | cons_cons h_ahd h_tl =>
      -- Rebuild the extended chain by applying the head link and using the inductive hypothesis.
      constructor
      · exact h_ahd
      · exact ih hd h_tl

theorem aux_list_regroup {α : Type*} (a x y : α) (L : List α) :
  a :: (L ++ [x, y]) = (a :: (L ++ [x])) ++ [y] :=
by
  rw [List.cons_append, List.append_assoc]
  rfl

theorem aux_nodup_append_last {α : Type*} (a : α) (L : List α) (x y : α)
  (h1 : (a :: (L ++ [x])).Nodup)
  (h2 : y ∉ a :: (L ++ [x])) :
  (a :: (L ++ [x, y])).Nodup :=
by
  -- Restructure the list concatenation
  rw [aux_list_regroup]

  -- Deconstruct the Nodup condition for list appending
  rw [List.nodup_append]
  refine ⟨h1, by simp, ?_⟩

  -- Prove the disjointness between `(a :: (L ++ [x]))` and `[y]`
  intro z hz1 w hw
  cases hw with
  | head =>
    -- The case where `w = y`
    intro hzy
    subst hzy
    exact h2 hz1
  | tail _ h =>
    -- The case where `w ∈ []` which is impossible
    cases h

theorem s_in_append_singleton_lem {n : ℕ} (L : List (GameString n)) (s : GameString n) : s ∈ L ++ [s] :=
by
  simp

theorem nodup_not_mem_tail_lem {n : ℕ} {a : GameString n} {l : List (GameString n)} (h : (a :: l).Nodup) : a ∉ l :=
fun ha => List.not_nodup_cons_of_mem ha h

theorem aux_s_neq_init {n : ℕ} (L : List (GameString n)) (s : GameString n)
  (h_nodup : (initialState n :: (L ++ [s])).Nodup) : s ≠ initialState n :=
by
  intro h

  -- From the no-duplicate hypothesis, the head cannot be in the tail
  have h_notin : initialState n ∉ L ++ [s] := nodup_not_mem_tail_lem h_nodup

  -- An element is always present if it was just appended to the list
  have h_in : s ∈ L ++ [s] := s_in_append_singleton_lem L s

  -- Using our false assumption `s = initialState n`, rewrite the element in the membership claim
  have h_in2 : initialState n ∈ L ++ [s] := by
    rw [← h]
    exact h_in

  -- We now have both `initialState n ∈ L ++ [s]` and `initialState n ∉ L ++ [s]`, causing a contradiction
  exact h_notin h_in2

theorem exists_ne_zero_of_ne_initialState {n : ℕ} (x : GameString n) (hx : x ≠ initialState n) :
  ∃ i : Fin n, x i ≠ 0 :=
by
  by_contra h
  push_neg at h
  apply hx
  funext i
  exact h i

theorem filter_nonempty_of_exists {n : ℕ} (x : GameString n) (h : ∃ i : Fin n, x i ≠ 0) :
  (Finset.filter (fun i => x i ≠ 0) Finset.univ).Nonempty :=
by
  rcases h with ⟨i, hi⟩
  use i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact hi

theorem firstNonZero_not_none {n : ℕ} (x : GameString n) (h : ∃ i : Fin n, x i ≠ 0) :
  firstNonZero x ≠ none :=
by
  simp only [firstNonZero]
  split
  · intro h_eq
    contradiction
  · have hS := filter_nonempty_of_exists x h
    contradiction

theorem firstNonZero_some_of_exists {n : ℕ} (x : GameString n) (h : ∃ i : Fin n, x i ≠ 0) :
  ∃ i : Fin n, firstNonZero x = some i :=
by
  have h_not_none := firstNonZero_not_none x h
  generalize h_eq : firstNonZero x = o
  cases o with
  | none => exact False.elim (h_not_none h_eq)
  | some val => exact ⟨val, rfl⟩

theorem firstNonZero_eq_some {n : ℕ} (x : GameString n) (hx : x ≠ initialState n) :
  ∃ i : Fin n, firstNonZero x = some i :=
firstNonZero_some_of_exists x (exists_ne_zero_of_ne_initialState x hx)

theorem firstNonZero_prop {n : ℕ} (x : GameString n) (i : Fin n) (hi : firstNonZero x = some i) :
  x i ≠ 0 :=
by
  unfold firstNonZero at hi
  -- Reduces any local `let` bindings from the definition
  dsimp only at hi
  -- Splits the if-then-else inside the definition of firstNonZero
  split at hi
  case isTrue h =>
    -- hi is now `some (S.min' h) = some i`
    injection hi with heq
    -- The minimum element of a non-empty set is a member of that set
    have h_mem := Finset.min'_mem _ h
    rw [heq] at h_mem
    -- Unpack the filter membership to extract the exact non-zero property
    exact (Finset.mem_filter.mp h_mem).2
  case isFalse h =>
    -- hi is now `none = some i`, which is impossible
    contradiction

theorem M_eq_update {n : ℕ} (x : GameString n) (i : Fin n) (hi : firstNonZero x = some i) :
  M x = Function.update x i (if x i = 1 then (2 : Fin 3) else (1 : Fin 3)) :=
by
  simp [M, hi]

theorem fin3_update_val_neq (a : Fin 3) :
  a ≠ (if a = 1 then (2 : Fin 3) else (1 : Fin 3)) :=
by
  by_cases h : a = 1
  · -- Case 1: a = 1
    -- Substitute `a` with `1` in the goal.
    rw [h]
    -- The goal becomes `1 ≠ (if 1 = 1 then 2 else 1)`.
    -- Since all variables are substituted with concrete literal numbers, Lean can decide this.
    decide
  · -- Case 2: a ≠ 1
    -- The simplifier uses the negated hypothesis `h` to rewrite the `if` condition to `False`,
    -- simplifying the RHS to `1 : Fin 3`. The goal becomes `a ≠ 1`, matching exactly our hypothesis `h`.
    simp [h]

theorem fin3_update_val_adj (a : Fin 3) (ha : a ≠ 0) :
  a.val + 1 = (if a = 1 then (2 : Fin 3) else (1 : Fin 3)).val ∨
  (if a = 1 then (2 : Fin 3) else (1 : Fin 3)).val + 1 = a.val :=
by
  by_cases h : a = 1
  · -- Case 1: `a = 1`
    left
    -- The condition `a = 1` evaluates to true, so we simplify the `if-then-else` expression.
    rw [if_pos h]
    -- We can directly substitute `a` with `1`.
    rw [h]
    -- The goal becomes `(1 : Fin 3).val + 1 = (2 : Fin 3).val`, i.e., `1 + 1 = 2`, which omega natively solves.
    omega
  · -- Case 2: `a ≠ 1` (which, together with `a ≠ 0`, forces `a.val = 2`)
    right
    -- The condition `a = 1` evaluates to false, so we simplify the `if-then-else` expression.
    rw [if_neg h]
    -- The goal is now `(1 : Fin 3).val + 1 = a.val`.
    -- `omega` natively understands `a : Fin 3` implies `a.val < 3`,
    -- and converts the hypotheses `a ≠ 0` and `a ≠ 1` to close the arithmetic bound `2 = a.val`.
    omega

theorem isValidMove_update {n : ℕ} (x : GameString n) (i : Fin n) (hxi : x i ≠ 0) :
  isValidMove x (Function.update x i (if x i = 1 then (2 : Fin 3) else (1 : Fin 3))) :=
by
  have h_self : Function.update x i (if x i = 1 then (2 : Fin 3) else (1 : Fin 3)) i = (if x i = 1 then (2 : Fin 3) else (1 : Fin 3)) := by simp
  have h_ne : ∀ j, j ≠ i → Function.update x i (if x i = 1 then (2 : Fin 3) else (1 : Fin 3)) j = x j := by
    intro j hj
    simp [hj]
  constructor
  · use i
    dsimp only
    constructor
    · rw [h_self]
      exact fin3_update_val_neq (x i)
    · intro j hj
      by_cases h : j = i
      · exact h
      · rw [h_ne j h] at hj
        exact False.elim (hj rfl)
  · intro j hj
    by_cases h : j = i
    · rw [h]
      rw [h_self]
      exact fin3_update_val_adj (x i) hxi
    · rw [h_ne j h] at hj
      exact False.elim (hj rfl)

theorem aux_isValidMove_M {n : ℕ} (x : GameString n) (hx : x ≠ initialState n) :
  isValidMove x (M x) :=
by
  -- 1. Get the first non-zero index
  obtain ⟨i, hi⟩ := firstNonZero_eq_some x hx
  -- 2. Rewrite M x in terms of our function update definition
  rw [M_eq_update x i hi]
  -- 3. The goal is now exactly what isValidMove_update provides
  -- We just need to prove that the element x i is indeed non-zero using our firstNonZero_prop lemma
  exact isValidMove_update x i (firstNonZero_prop x i hi)

theorem firstNonZero_initialState {n : ℕ} : firstNonZero (initialState n) = none :=
by
  simp [firstNonZero, initialState]

theorem M_initialState {n : ℕ} : M (initialState n) = initialState n :=
by
  unfold M
  simp [firstNonZero_initialState]

theorem M_eval_none {n : ℕ} (x : GameString n) (h : firstNonZero x = none) : M x = x :=
by
  unfold M
  simp [h]

theorem fin3_toggle_toggle (a : Fin 3) (h : a ≠ 0) : (if (if a = 1 then (2 : Fin 3) else (1 : Fin 3)) = 1 then (2 : Fin 3) else (1 : Fin 3)) = a :=
by
  -- Determine that the only possible valid values for `a` are 1 and 2
  have ha : a = 1 ∨ a = 2 := by
    -- Extract the upper bound `a < 3` and evaluate the non-zero condition
    have h1 : a.val < 3 := a.isLt
    have h2 : a.val ≠ 0 := by
      intro h_eq
      apply h
      ext
      change a.val = 0
      exact h_eq

    -- Utilize `omega`'s decision procedure on the natural numbers to branch `a`
    have h3 : a.val = 1 ∨ a.val = 2 := by omega

    -- Transfer the cases back from `.val` integers (Nat) to `Fin 3`
    rcases h3 with h3 | h3
    · left
      ext
      change a.val = 1
      exact h3
    · right
      ext
      change a.val = 2
      exact h3

  -- Exhaustively check the remaining finite cases utilizing `rfl`
  rcases ha with h_eq | h_eq
  · rw [h_eq]
    rfl
  · rw [h_eq]
    rfl

theorem dite_min'_eq {n : ℕ} (Sx Sy : Finset (Fin n)) (h : Sx = Sy) :
  (if hx : Sx.Nonempty then some (Sx.min' hx) else none) =
  (if hy : Sy.Nonempty then some (Sy.min' hy) else none) :=
by
  subst h
  rfl

theorem firstNonZero_eq_of_cond_eq {n : ℕ} (x y : GameString n) (h : ∀ j, x j ≠ 0 ↔ y j ≠ 0) :
  firstNonZero x = firstNonZero y :=
by
  simp only [firstNonZero]
  apply dite_min'_eq
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact h i

theorem fin3_one_neq_zero : (1 : Fin 3) ≠ 0 :=
by
  decide

theorem fin3_two_neq_zero : (2 : Fin 3) ≠ 0 :=
by
  decide

theorem fin3_ite_neq_zero {c : Prop} [Decidable c] : (if c then (2 : Fin 3) else (1 : Fin 3)) ≠ 0 :=
by
  by_cases hc : c
  · rw [if_pos hc]
    exact fin3_two_neq_zero
  · rw [if_neg hc]
    exact fin3_one_neq_zero

theorem M_eval_none_my {n : ℕ} (x : GameString n) (j : Fin n) (h : firstNonZero x = none) :
  M x j = x j :=
by
  unfold M
  simp [h]

theorem M_eq_update_my {n : ℕ} (x : GameString n) (j : Fin n) (i : Fin n) (h : firstNonZero x = some i) :
  M x j = Function.update x i (if x i = 1 then (2 : Fin 3) else (1 : Fin 3)) j :=
by
  simp [M, h]

theorem firstNonZero_mem_filter {n : ℕ} (x : GameString n) (i : Fin n) (h : firstNonZero x = some i) :
  i ∈ Finset.univ.filter (fun j => x j ≠ 0) :=
by
  dsimp only [firstNonZero] at h
  split_ifs at h with h_nonempty
  injection h with h_eq
  rw [← h_eq]
  exact Finset.min'_mem _ h_nonempty

theorem firstNonZero_prop_aux {n : ℕ} (x : GameString n) (i : Fin n) (h : firstNonZero x = some i) : x i ≠ 0 :=
(Finset.mem_filter.mp (firstNonZero_mem_filter x i h)).2

theorem firstNonZero_some_implies_mem_my {n : ℕ} (x : GameString n) (i : Fin n)
  (h : firstNonZero x = some i) :
  i ∈ Finset.univ.filter (fun j => x j ≠ 0) :=
by
  -- The membership of `Finset.filter` breaks down to being in the original set (`Finset.univ`)
  -- and satisfying the filter predicate (`x i ≠ 0`).
  rw [Finset.mem_filter]

  -- `Finset.mem_univ i` is trivially true, and the second property is handled by our aux lemma.
  exact ⟨Finset.mem_univ i, firstNonZero_prop_aux x i h⟩

theorem firstNonZero_prop_my {n : ℕ} (x : GameString n) (i : Fin n) (h : firstNonZero x = some i) :
  x i ≠ 0 :=
by
  have h_mem := firstNonZero_some_implies_mem_my x i h
  exact (Finset.mem_filter.mp h_mem).2

theorem update_same_my {α : Type _} {β : α → Type _} [DecidableEq α] {f : (a : α) → β a} {a : α} {v : β a} :
  Function.update f a v a = v :=
by
  simp [Function.update]

theorem update_noteq_my {α : Type _} {β : α → Type _} [DecidableEq α] {f : (a : α) → β a} {a a' : α} {v : β a} (h : a' ≠ a) :
  Function.update f a v a' = f a' :=
by
  simp [h]

theorem M_x_neq_zero_iff_x_neq_zero {n : ℕ} (x : GameString n) (j : Fin n) :
  M x j ≠ 0 ↔ x j ≠ 0 :=
by
  cases h : firstNonZero x with
  | none =>
    -- Case 1: firstNonZero x = none
    rw [M_eval_none_my x j h]
  | some i =>
    -- Case 2: firstNonZero x = some i
    rw [M_eq_update_my x j i h]
    by_cases hij : j = i
    · -- Subcase 2a: j = i
      rw [hij]
      rw [update_same_my]
      have h_nz := firstNonZero_prop_my x i h
      have h_ite := fin3_ite_neq_zero (c := (x i = 1))
      constructor
      · intro _
        exact h_nz
      · intro _
        exact h_ite
    · -- Subcase 2b: j ≠ i
      rw [update_noteq_my hij]

theorem firstNonZero_M_eq {n : ℕ} (x : GameString n) : firstNonZero (M x) = firstNonZero x :=
firstNonZero_eq_of_cond_eq (M x) x (fun j => M_x_neq_zero_iff_x_neq_zero x j)

theorem M_eq_update_lem {n : ℕ} (x : GameString n) (i : Fin n) (h : firstNonZero x = some i) :
  M x = Function.update x i (if x i = 1 then (2 : Fin 3) else (1 : Fin 3)) :=
by
  unfold M
  simp [h]

theorem firstNonZero_prop_lem {n : ℕ} (x : GameString n) (i : Fin n) (h : firstNonZero x = some i) :
  x i ≠ 0 :=
by
  unfold firstNonZero at h
  dsimp only at h
  split at h
  · rename_i hn
    -- Given that it found `some`, inject the Option to extract the internal equality
    injection h with h_eq
    -- A minimum element of a Finset must belong to the Finset itself
    have H_mem := Finset.min'_mem _ hn
    -- Substitute our specific `i` into this membership property
    rw [h_eq] at H_mem
    -- The set `S` is formed using `Finset.filter`, its membership trivially bounds our target
    exact (Finset.mem_filter.mp H_mem).2
  · -- If the set was empty, `firstNonZero` evaluates to `none`, making `h` impossible
    contradiction

theorem update_same_lem {n : ℕ} {x : GameString n} {i : Fin n} {v : Fin 3} :
  Function.update x i v i = v :=
by
  simp

theorem update_noteq_lem {n : ℕ} {x : GameString n} {i j : Fin n} {v : Fin 3} (h : j ≠ i) :
  Function.update x i v j = x j :=
by
  simp [h]

theorem M_M_eq {n : ℕ} (x : GameString n) : M (M x) = x :=
by
  cases h : firstNonZero x with
  | none =>
    have h1 := M_eval_none x h
    rw [h1, h1]
  | some i =>
    -- Expand M x as a targeted update
    have h2 := M_eq_update_lem x i h

    -- Show that the first non-zero index remains identically `some i` after one application
    have h3 : firstNonZero (M x) = some i := by rw [firstNonZero_M_eq x, h]

    -- Expand M (M x) as an update at the exact same index `some i`
    have h4 := M_eq_update_lem (M x) i h3

    -- Evaluate point-wise equivalence using functional extensionality
    funext j
    by_cases hj : j = i
    · -- Case: `j = i` (the modified index toggled twice)
      -- Use `rw` instead of `subst` to prevent Lean from erasing `i` or `j` from the context
      rw [hj]

      -- Expose the first outer application explicitly for `i`
      rw [h4]
      rw [update_same_lem]

      -- Expose the inner original layer explicitly for `i`
      rw [h2]
      rw [update_same_lem]

      -- Perform the logical toggle mapping
      apply fin3_toggle_toggle
      exact firstNonZero_prop_lem x i h

    · -- Case: `j ≠ i` (untouched indices simply pass through functionally identically)
      -- Evaluate the outer pass-through
      rw [h4]
      rw [update_noteq_lem hj]

      -- Evaluate the inner pass-through
      rw [h2]
      rw [update_noteq_lem hj]

theorem fin3_update_neq (y : Fin 3) (hy : y ≠ 0) (h : (if y = 1 then (2 : Fin 3) else (1 : Fin 3)) = y) : False :=
by
  revert h hy y
  decide

theorem M_neq_self_of_neq_init {n : ℕ} (x : GameString n) (hx : x ≠ initialState n) : M x ≠ x :=
by
  intro h

  -- 1. Show that since x ≠ initial state, the subset of non-zero elements is Nonempty
  have h_nonempty : (Finset.univ.filter (fun i => x i ≠ 0)).Nonempty := by
    by_contra h_empty
    apply hx
    funext j
    have h_x_eq_0 : x j = 0 := by
      by_contra h_neq
      have h_mem : j ∈ Finset.univ.filter (fun i => x i ≠ 0) := by
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ j, h_neq⟩
      exact h_empty ⟨j, h_mem⟩
    exact h_x_eq_0

  -- 2. Define the index `i` of the first non-zero element
  let i := (Finset.univ.filter (fun i => x i ≠ 0)).min' h_nonempty
  have h_firstNonZero : firstNonZero x = some i := by
    change (if h : (Finset.univ.filter (fun i => x i ≠ 0)).Nonempty then some ((Finset.univ.filter (fun i => x i ≠ 0)).min' h) else (none : Option (Fin n))) = some i
    rw [dif_pos h_nonempty]

  -- 3. Unfold M, evaluate it at the extracted index `i`, and simplify via equality
  have h_M : M x = Function.update x i (if x i = 1 then (2 : Fin 3) else (1 : Fin 3)) := by
    unfold M
    simp [h_firstNonZero]

  -- 4. Rewrite the main equality using `h_M` and standard Function properties
  have h_i : M x i = x i := congr_fun h i
  rw [h_M] at h_i
  rw [Function.update_self] at h_i

  -- 5. Extract the non-zero invariant bound for `x i`
  have h_x_ne_0 : x i ≠ 0 := by
    have h_mem_filter : i ∈ Finset.univ.filter (fun i => x i ≠ 0) := Finset.min'_mem (Finset.univ.filter (fun i => x i ≠ 0)) h_nonempty
    rw [Finset.mem_filter] at h_mem_filter
    exact h_mem_filter.2

  -- 6. Apply our `Fin 3` computational lemma to arrive at the final contradiction
  exact fin3_update_neq (x i) h_x_ne_0 h_i

theorem M_mem_L_of_mem_L {n : ℕ} (L : List (GameString n)) (hBob : BobPairs L) (x : GameString n) (hx : x ∈ L) : M x ∈ L :=
by
  -- We revert `hx` so that the induction hypothesis is correctly generalized for any element in `rest`.
  revert hx
  induction hBob with
  | nil =>
    intro hx
    cases hx
  | cons s1 s2 rest heq _ ih =>
    intro hx
    -- Use the equality provided by the constructor to substitute `s2` with `M s1` uniformly
    cases heq

    -- Simplify the membership condition to an explicit disjunction
    simp only [List.mem_cons] at hx ⊢

    cases hx with
    | inl h1 =>
      -- Subcase: x = s1
      rw [h1]
      right
      left
      rfl
    | inr h2 =>
      cases h2 with
      | inl h3 =>
        -- Subcase: x = s2 (which has been substituted to M s1)
        rw [h3]
        left
        -- Applying `M` to `M s1` results back in `s1`
        rw [M_M_eq]
      | inr h4 =>
        -- Subcase: x ∈ rest
        right
        right
        -- Apply the inductive hypothesis
        exact ih h4

theorem nodup_tail_of_nodup_cons {α : Type*} (a : α) (L : List α) (h : (a :: L).Nodup) : L.Nodup :=
by
  cases h
  assumption

theorem not_mem_of_nodup_append_singleton {α : Type*} (L : List α) (s : α) (h : (L ++ [s]).Nodup) : s ∉ L :=
by
  induction L with
  | nil =>
    intro hs
    -- The list is empty, so `s ∈ []` is trivially false.
    cases hs
  | cons x xs ih =>
    intro hs
    -- `(x :: xs) ++ [s]` evaluates to `x :: (xs ++ [s])`.
    -- We can extract the disjointness and nodup properties explicitly.
    rw [List.cons_append, List.nodup_cons] at h
    rw [List.mem_cons] at hs
    cases hs with
    | inl heq =>
      subst heq
      -- We now have `h.1 : s ∉ xs ++ [s]`. We construct the proof that `s ∈ xs ++ [s]` for the contradiction.
      exact h.1 (List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))
    | inr hmem =>
      -- By the inductive hypothesis, `(xs ++ [s]).Nodup` implies `s ∉ xs`, contrasting our condition.
      exact ih h.2 hmem

theorem aux_s_notin_L {n : ℕ} (L : List (GameString n)) (s : GameString n) (h_nodup : (initialState n :: (L ++ [s])).Nodup) : s ∉ L :=
not_mem_of_nodup_append_singleton L s (nodup_tail_of_nodup_cons (initialState n) (L ++ [s]) h_nodup)

theorem aux_s_neq_init_2 {n : ℕ} (L : List (GameString n)) (s : GameString n) (h_nodup : (initialState n :: (L ++ [s])).Nodup) : s ≠ initialState n :=
by
  intro h
  -- From the Nodup hypothesis on the constructed list, the head element is not in the tail.
  have h1 : initialState n ∉ L ++ [s] := (List.nodup_cons.mp h_nodup).1

  -- By substituting our contradictory assumption `h`, we claim `initialState n` is actually in the tail.
  have h2 : initialState n ∈ L ++ [s] := by
    rw [←h]
    -- `simp` easily proves `s ∈ L ++ [s]` by reducing to `s ∈ L ∨ s ∈ [s]` and finally `True`.
    simp

  -- We now have a direct contradiction.
  exact h1 h2

theorem mem_cons_append_singleton {α : Type*} (x : α) (a : α) (L : List α) (b : α) :
  x ∈ a :: (L ++ [b]) → x = a ∨ x ∈ L ∨ x = b :=
by
  intro h
  simp_all

theorem aux_not_mem_M_s {n : ℕ} (L : List (GameString n)) (s : GameString n)
  (h_nodup : (initialState n :: (L ++ [s])).Nodup)
  (h_Bob : BobPairs L) :
  M s ∉ initialState n :: (L ++ [s]) :=
by
  intro h_in
  have h_s_neq : s ≠ initialState n := aux_s_neq_init_2 L s h_nodup
  have h_in_or : M s = initialState n ∨ M s ∈ L ∨ M s = s := mem_cons_append_singleton (M s) (initialState n) L s h_in
  cases h_in_or with
  | inl h1 =>
    have h_M_M : M (M s) = M (initialState n) := by rw [h1]
    rw [M_M_eq] at h_M_M
    rw [M_initialState] at h_M_M
    exact h_s_neq h_M_M
  | inr h_or =>
    cases h_or with
    | inl h2 =>
      have h_M_s_in : M (M s) ∈ L := M_mem_L_of_mem_L L h_Bob (M s) h2
      rw [M_M_eq] at h_M_s_in
      have h_s_notin : s ∉ L := aux_s_notin_L L s h_nodup
      exact h_s_notin h_M_s_in
    | inr h3 =>
      have h_neq : M s ≠ s := M_neq_self_of_neq_init s h_s_neq
      exact h_neq h3

theorem IsValidGamePlay_append_M_aux {n : ℕ} (L : List (GameString n)) (s : GameString n)
  (h_valid : IsValidGamePlay (L ++ [s])) (hBob : BobPairs L) :
  IsValidGamePlay (L ++ [s, M s]) :=
by
  -- Destruct the valid game play property into its Chain and Nodup conditions
  have ⟨h_chain, h_nodup⟩ := h_valid

  -- Use the helper lemmas to deduce the intermediate conditions
  have h_neq := aux_s_neq_init L s h_nodup
  have h_move := aux_isValidMove_M s h_neq
  have h_not_mem := aux_not_mem_M_s L s h_nodup hBob

  -- Extend the Chain and Nodup properties with M(s)
  have h_chain2 := aux_chain_append_last isValidMove (initialState n) L s (M s) h_chain h_move
  have h_nodup2 := aux_nodup_append_last (initialState n) L s (M s) h_nodup h_not_mem

  -- Assemble back the extended valid game play
  exact ⟨h_chain2, h_nodup2⟩

theorem BobPairs_append_M_aux {n : ℕ} (L : List (GameString n)) (s : GameString n)
  (hBob : BobPairs L) : BobPairs (L ++ [s, M s]) :=
by
  induction hBob
  · constructor
    · rfl
    · constructor
  · constructor
    · assumption
    · assumption

theorem HasWinningStrategy_implies_not_BobPairs {n : ℕ} (play : List (GameString n))
  (h_win : HasWinningStrategy n play) :
  ¬ BobPairs play :=
by
  -- Proceed by induction on the winning strategy hypothesis
  induction h_win with
  | win play s h_valid h_all ih =>
    -- Assume for contradiction that `play` currently consists of Bob pairs
    intro h_Bob

    -- Using the auxiliary lemma, Bob responding with `M s` yields a valid game state
    have h_valid_Ms := IsValidGamePlay_append_M_aux play s h_valid h_Bob

    -- Using the auxiliary lemma `BobPairs_append_M_aux` defined above,
    -- the resulting sequence still consists of Bob pairs
    have h_Bob_append := BobPairs_append_M_aux play s h_Bob

    -- The induction hypothesis states that any valid response by Bob will lead to a sequence
    -- that is *not* composed entirely of Bob pairs. We supply `M s` and the validity proof
    -- to the induction hypothesis to get a contradiction.
    exact ih (M s) h_valid_Ms h_Bob_append

theorem AliceHasWinningStrategy_false {n : ℕ} : ¬ AliceHasWinningStrategy n :=
by
  intro h
  exact HasWinningStrategy_implies_not_BobPairs [] h BobPairs.nil

theorem putnam_2025_a3 (n : ℕ) (hn : 1 ≤ n) : putnam_2025_a3_solution n ↔ AliceHasWinningStrategy n :=
by
  constructor
  · intro h
    change false = true at h
    contradiction
  · intro h
    exact False.elim (AliceHasWinningStrategy_false h)
