
def bubbleSort [Ord α] (arr : Array α) : Array α :=
  let rec loop₁ [Ord α] (arr : Array α) (i : Nat) : Array α :=
    let rec loop₂ [Ord α] (arr : Array α) (i : Nat) (j : Nat) : Array α :=
      if h_index : j < arr.size - 1 - i then
        match Ord.compare arr[j] arr[j + 1] with
        |.gt => loop₂ (arr.swap j (j + 1)) i (j + 1)
        |.lt |.eq => loop₂ arr i (j + 1)
      else
        arr
    if i < arr.size then
      loop₁ (loop₂ arr i 0) (i + 1)
    else
      arr
  termination_by arr.size - i
  decreasing_by
    have loop₂_size_eq (arr' arr : Array α) (i j : Nat) (h_size : arr'.size = arr.size) :
      (bubbleSort.loop₁.loop₂ arr' i j).size = arr.size := by
      generalize hk : arr'.size - 1 - i - j = k
      induction k generalizing arr' i j <;> unfold bubbleSort.loop₁.loop₂
      case zero =>
        split
        case isTrue hlt =>
          have hnez : arr'.size - 1 - i - j ≠ 0 := by exact Nat.sub_ne_zero_iff_lt.mpr hlt
          contradiction
        case isFalse hnlt => exact h_size
      case succ n ih =>
        split
        case isTrue hlt =>
          have h_eq_n : arr'.size - 1 - i - (j + 1) = n := by
            calc arr'.size - 1 - i - (j + 1)
              _ = (arr'.size - 1 - i - j) - 1 := rfl
              _ = n := Nat.sub_eq_of_eq_add hk
          split
          case h_1 =>
            have h_size_swap : (arr'.swap j (j + 1)).size = arr'.size := arr'.size_swap j (j + 1)
            apply ih
            case h_size => exact h_size_swap.trans h_size
            case hk =>
              rw[h_size_swap]
              exact h_eq_n
          case h_2 =>
            apply ih
            case h_size => exact h_size
            case hk => exact h_eq_n
          case h_3 =>
            apply ih
            case h_size => exact h_size
            case hk => exact h_eq_n
        case isFalse hnlt =>
          have : j < arr'.size - 1 - i := Nat.lt_of_sub_eq_succ hk
          contradiction
    rw[loop₂_size_eq arr arr i 0 rfl]
    rename_i h
    exact Nat.sub_succ_lt_self arr.size i h
  loop₁ arr 0

def bubbleSortif [LT α]  [∀(a b : α), Decidable (a > b)] (arr : Array α) : Array α :=
  let rec loop₁ [LT α]  [∀(a b : α), Decidable (a > b)] (arr : Array α) (i : Nat) : Array α :=
    let rec loop₂ [LT α]  [∀(a b : α), Decidable (a > b)] (arr : Array α) (i : Nat) (j : Nat) : Array α :=
      if h_index : j < arr.size - 1 - i then
        if arr[j] > arr[j + 1] then
          loop₂ (arr.swap j (j + 1)) i (j + 1)
        else
          loop₂ arr i (j + 1)
      else
        arr
    if i < arr.size then
      loop₁ (loop₂ arr i 0) (i + 1)
    else
      arr
  termination_by arr.size - i
  decreasing_by
    have loop₂_size_eq (arr' arr : Array α) (i j : Nat) (h_size : arr'.size = arr.size) :
      (bubbleSortif.loop₁.loop₂ arr' i j).size = arr.size := by
      generalize hk : arr'.size - 1 - i - j = k
      induction k generalizing arr' i j <;> unfold bubbleSortif.loop₁.loop₂
      case zero =>
        split
        case isTrue hlt =>
          have h_ne_z : arr'.size - 1 - i - j ≠ 0 := Nat.sub_ne_zero_iff_lt.mpr hlt
          contradiction
        case isFalse =>
          exact h_size
      case succ n ih =>
        split
        case isTrue hlt =>
          have h_eq_n : arr'.size - 1 - i - (j + 1) = n := by omega
          split
          case isTrue =>
            have h_size_swap : (arr'.swap j (j + 1)).size = arr'.size := Array.size_swap arr' j (j + 1)
            apply ih
            case h_size =>
              exact h_size_swap.trans h_size
            case hk =>
              rw[h_size_swap]
              exact h_eq_n
          case isFalse =>
            apply ih
            case h_size => exact h_size
            case hk => exact h_eq_n
        case isFalse =>
          have : j < arr'.size - 1 - i := Nat.lt_of_sub_eq_succ hk
          contradiction
    rw[loop₂_size_eq arr arr i 0 rfl]
    rename_i h
    exact Nat.sub_succ_lt_self arr.size i h
  loop₁ arr 0

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

namespace NotZenn

def bubbleSort_for [Inhabited α] [Ord α] (arr : Array α) : Array α := Id.run do
  let mut arr := arr
  for i in [0:arr.size] do
    for j in [0:arr.size - 1 - i] do
      match Ord.compare arr[j]! arr[j + 1]! with
      |.gt => arr := arr.swapIfInBounds j (j + 1)
      |.lt |.eq => pure ()
  arr

def bubbleSort [Ord α] (arr : Array α) : Array α :=
  let rec loop₁ [Ord α] (arr : Array α) (i : Nat) : Array α :=
    let rec loop₂ [Ord α] (arr : Array α) (i j : Nat) :=
      if h₁ : j < arr.size - 1 - i then
        -- haveI j_lt_arr_size_pred : j < arr.size - 1 := lt_of_lt_sub h₁
        -- haveI succ_j_lt_arr_size : j + 1 < arr.size := Nat.add_lt_of_lt_sub j_lt_arr_size_pred
        match Ord.compare arr[j] arr[j + 1] with
        |.gt =>
          -- haveI swap_size_eq : arr.size = (arr.swap j (j + 1)).size := Eq.symm (Array.size_swap arr j (j + 1))
          -- haveI succ_j_lt_swapped : j + 1 < (arr.swap j (j + 1)).size := Nat.lt_of_lt_of_eq succ_j_lt_arr_size swap_size_eq
          loop₂ (arr.swap j (j + 1)) i (j + 1)
        |.lt |.eq => loop₂ arr i (j + 1)
      else
        arr
    termination_by arr.size - 1 - i - j
    if h : i < arr.size then
      loop₁ (loop₂ arr i 0) (i + 1)
    else
      arr
  termination_by arr.size - i
  decreasing_by
    have loop₂_size_eq {arr' arr : Array α} {i j : Nat} (h_size : arr'.size = arr.size) : (bubbleSort.loop₁.loop₂ arr' i j).size = arr.size := by
      generalize h : arr'.size - 1 - i - j = k
      induction k generalizing arr' i j
      case zero =>
        unfold bubbleSort.loop₁.loop₂
        split
        case isTrue h₁ =>
          have h₃ : arr'.size - 1 - i - j ≠ 0 := Nat.sub_ne_zero_iff_lt.mpr h₁
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
            have h_size_swap : (arr'.swap j (j + 1)).size = arr'.size := arr'.size_swap j (j + 1)
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
    rw[loop₂_size_eq rfl]
    exact Nat.sub_succ_lt_self arr.size i h
  loop₁ arr 0

#eval bubbleSort_for #[100,90,45,32,56,44]
#eval bubbleSort #[100,90,45,32,56,44]

end NotZenn
