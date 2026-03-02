import Mathlib.Data.Finset.Fold

-- Finset.foldに関する補題を探す
#check Finset.fold_empty
#check Finset.fold_singleton
#check Finset.fold_image

-- Multiset.foldに関する補題を探す
#check Multiset.fold_replicate
#check Multiset.fold_zero

-- List.foldlに関する補題を探す
#check List.foldl_nil
#check List.foldl_cons
#check List.foldl_append

-- 定数関数のfold
#check Finset.fold_const

-- 空集合の性質
#check Finset.empty_union
#check Finset.union_empty
