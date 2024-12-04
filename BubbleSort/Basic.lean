def hello := "world"

theorem lt_of_lt_sub {a b c : Nat} : a < b - c → a < b := by
  intro h
  cases Nat.le_total b c with
  | inl hbc =>
    have : b - c = 0 := Nat.sub_eq_zero_of_le hbc
    rw [this] at h
    exact absurd h (Nat.not_lt_zero a)
  | inr hcb =>
    calc
      a < b - c := h
      b - c ≤ b := Nat.sub_le b c

def bubbleSort_for [Inhabited α] [Ord α] (arr : Array α) : Array α := Id.run do
  let mut arr := arr
  for i in [0:arr.size] do
    for j in [0:arr.size-1-i] do
      match Ord.compare arr[j]! arr[j+1]! with
      |.gt => arr := arr.swap! j (j + 1)
      |.lt |.eq => pure ()
  arr

def bubbleSort [Ord α] (arr : Array α) : Array α :=
  let rec loop₁ [Ord α] (arr : Array α) (i : Nat) : Array α :=
    let rec loop₂ [Ord α] (arr : Array α) (i j : Fin arr.size) :=
      if h₁ : j < arr.size - 1 - i then
        haveI j_lt_arr_size_pred : j < arr.size - 1 := lt_of_lt_sub h₁
        haveI succ_j_lt_arr_size : j + 1 < arr.size := Nat.add_lt_of_lt_sub j_lt_arr_size_pred
        match Ord.compare arr[j] arr[↑j + 1] with
        |.gt =>
          haveI swap_size_eq : arr.size = (arr.swap j ⟨↑j + 1, succ_j_lt_arr_size⟩).size := Eq.symm (Array.size_swap arr j ⟨↑j + 1, succ_j_lt_arr_size⟩)
          haveI succ_j_lt_swapped : ↑j + 1 < (arr.swap j ⟨↑j + 1, succ_j_lt_arr_size⟩).size := Nat.lt_of_lt_of_eq succ_j_lt_arr_size swap_size_eq
          loop₂ (arr.swap j ⟨j + 1, succ_j_lt_arr_size⟩) (i.cast swap_size_eq) ⟨↑j + 1, succ_j_lt_swapped⟩
        |.lt |.eq => loop₂ arr i (⟨j + 1, succ_j_lt_arr_size⟩)
      else
        arr
    termination_by arr.size - 1 - i - j
    if h : i < arr.size then
      loop₁ (loop₂ arr ⟨i, h⟩ ⟨0, Nat.zero_lt_of_lt h⟩) (i + 1)
    else
      arr
  termination_by arr.size - i
  decreasing_by
    have loop₂_size_eq [Ord α] (arr' arr : Array α) {i j : Nat} {hi : i < arr'.size} {hj : j < arr'.size} (h_size : arr'.size = arr.size) : (bubbleSort.loop₁.loop₂ arr' ⟨i, hi⟩ ⟨j, hj⟩).size = arr.size := by
      generalize h : arr'.size - 1 - i - j = k
      induction k generalizing arr' i j
      case zero =>
        unfold bubbleSort.loop₁.loop₂
        split
        case isTrue h₁ =>
          have h₃ : arr'.size - 1 - i - j ≠ 0 := by exact Nat.sub_ne_zero_iff_lt.mpr h₁
          contradiction
        case isFalse =>
          exact h_size
      case succ n ih =>
        unfold bubbleSort.loop₁.loop₂
        split
        case isTrue h₁ =>
          have h_eq_n : arr'.size - 1 - i - (j + 1) = n := by
            calc
              arr'.size - 1 - i - (j + 1) = (arr'.size - 1 - i - j) - 1 := rfl
              _ = n := Nat.sub_eq_of_eq_add h
          split
          case h_1 =>
            have h_size_swap : (arr'.swap ⟨j, hj⟩ ⟨↑(⟨j, hj⟩ : Fin arr'.size) + 1, bubbleSort.loop₁.loop₂.proof_2 arr' ⟨i, hi⟩ ⟨j, hj⟩ h₁⟩).size = arr'.size :=
              arr'.size_swap ⟨j, hj⟩ ⟨↑(⟨j, hj⟩ : Fin arr'.size) + 1, bubbleSort.loop₁.loop₂.proof_2 arr' ⟨i, hi⟩ ⟨j, hj⟩ h₁⟩
            apply ih
            exact Eq.trans h_size_swap h_size
            rw[h_size_swap]
            exact h_eq_n
          case h_2 =>
            apply ih
            exact h_size
            exact h_eq_n
          case h_3 =>
            apply ih
            exact h_size
            exact h_eq_n
        case isFalse =>
          exact h_size
    rw[loop₂_size_eq arr arr rfl]
    exact Nat.sub_succ_lt_self arr.size i h
  loop₁ arr 0

#eval bubbleSort_for #[100,90,45,32,56,44]
#eval bubbleSort #[100,90,45,32,56,44]
