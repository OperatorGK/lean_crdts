import tactic

def gcounter (n: ℕ) : Type := array n ℕ

def inc {n: ℕ} (g: gcounter n) (index: fin n) (value: ℕ) : gcounter n :=
  g.write index $ g.read index + value

def merge {n: ℕ} (g₁: gcounter n) (g₂: gcounter n) : gcounter n :=
  array.map₂ max g₁ g₂

def value {n: ℕ} (g: gcounter n) : ℕ :=
  array.foldl g 0 (+)

lemma merge_idempotent {n: ℕ} (g: gcounter n) : merge g g = g :=
begin
  rw merge,
  ext1,
  simp,
end

lemma merge_commutative {n: ℕ} (g₁ g₂: gcounter n) : merge g₁ g₂ = merge g₂ g₁ :=
begin
  repeat {rw merge},
  ext1,
  simp,
  rw max_comm,
end

lemma merge_associative
 {n: ℕ} (g₁ g₂ g₃: gcounter n) : merge g₁ (merge g₂ g₃) = merge (merge g₁ g₂) g₃ :=
begin
  repeat {rw merge},
  ext1,
  simp,
  rw max_assoc,
end

lemma inc_merge_increasing
  {n: ℕ} (v: ℕ) (i: fin n) (g: gcounter n) : merge (inc g i v) g = inc g i v :=
begin
  rw merge,
  rw inc,
  ext1,
  simp,

  by_cases i = i_1,
  rw h,
  rw array.read_write,
  linarith,

  rwa array.read_write_of_ne,
end

lemma inc_value_increasing_aux₁
  (a b: ℕ) (li: list ℕ) : list.foldl (+) (a + b) li = list.foldl (+) a li + b :=
begin
  induction li generalizing a b,
  refl,

  rw list.foldl,
  rw add_right_comm,
  apply li_ih,
end

lemma inc_value_increasing_aux₂
  (a b i_val: ℕ) (li: list ℕ) (h: i_val < li.length):
  list.foldl has_add.add a (li.update_nth i_val (li.nth_le i_val h + b)) =
  list.foldl has_add.add a li + b :=
begin
  induction li generalizing a b i_val,
  
  rw list.length at h,
  linarith,
  
  cases i_val,
  all_goals {
    rw list.update_nth,
    rw list.nth_le,
    rw list.foldl,
    rw list.foldl,
  },

  rw ← add_assoc,
  apply inc_value_increasing_aux₁,
  apply li_ih,
end

lemma inc_value_increasing
  {n: ℕ} (v: ℕ) (i: fin n) (g: gcounter n) : value (inc g i v) = value g + v :=
begin
  rw inc,
  rw value,
  rw value,

  rw ← array.to_list_foldl,
  rw ← array.to_list_foldl,
  rw array.write_to_list,
  cases i,
  rw ← array.to_list_nth_le,
  any_goals { rwa array.to_list_length },

  generalize h : array.to_list g = li,

  conv {
    to_lhs,
    congr,
    skip,
    skip,
    congr,
    rw h,
    
    skip,
    skip,
    congr,
    congr,
    rw h,
  },

  conv {
    to_rhs,
    congr,
    congr,
    skip,
    skip,
    rw h,
  },

  conv {
    to_lhs,
    congr,
    funext,
    rw add_comm,
  }, 

  conv {
    to_rhs,
    congr,
    congr,
    funext,
    rw add_comm,
  },
  
  ring,

  apply inc_value_increasing_aux₂,
end
