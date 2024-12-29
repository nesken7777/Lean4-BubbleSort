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
    have loop₂_size_eq (arr : Array α) (i j : Nat) : (bubbleSort.loop₁.loop₂ arr i j).size = arr.size := by
      induction arr, i, j using bubbleSort.loop₁.loop₂.induct
      <;> unfold bubbleSort.loop₁.loop₂ <;> simp[*]
    rw[loop₂_size_eq]
    rename_i h
    exact Nat.sub_succ_lt_self arr.size i h
  loop₁ arr 0
