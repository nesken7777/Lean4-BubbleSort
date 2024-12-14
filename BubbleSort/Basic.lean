
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

def bubbleSortfor [Inhabited α] [Ord α] (arr : Array α) : Array α := Id.run do
  let mut arr := arr
  for i in [0:arr.size] do
    for j in [0:arr.size - 1 - i] do
      match Ord.compare arr[j]! arr[j + 1]! with
      |.gt => arr := arr.swapIfInBounds j (j + 1)
      |.lt |.eq => pure ()
  arr
