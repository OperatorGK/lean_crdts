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
  dsimp only [merge],
  apply array.ext,
  intro,
  simp only [array.read_map₂, max_eq_right, eq_self_iff_true],
end

lemma merge_commutative {n: ℕ} (g₁ g₂: gcounter n) : merge g₁ g₂ = merge g₂ g₁ :=
begin
  dsimp only [merge],
  apply array.ext,
  intro,
  simp only [array.read_map₂, max_comm],
end

lemma merge_associative
 {n: ℕ} (g₁ g₂ g₃: gcounter n) : merge g₁ (merge g₂ g₃) = merge (merge g₁ g₂) g₃ :=
begin
  dsimp only [merge],
  apply array.ext,
  intro,
  simp only [array.read_map₂, max_assoc],
end

lemma inc_merge_increasing
  {n: ℕ} (v: ℕ) (i: fin n) (g: gcounter n) : merge (inc g i v) g = inc g i v :=
begin
  dsimp only [merge, inc],
  apply array.ext,
  intro,
  simp only [array.read_map₂, max_eq_left_iff],

  by_cases i = i_1,
  simp only [h, array.read_write],
  linarith,

  rwa array.read_write_of_ne,
end

lemma inc_value_increasing_aux₁
  (a b: ℕ) (li: list ℕ) : list.foldl (+) (a + b) li = list.foldl (+) a li + b :=
begin
  induction li generalizing a b,
  refl,
  simp only [list.foldl, add_right_comm, li_ih],
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
  simp only [list.update_nth, list.nth_le, list.foldl, ← add_assoc],

  apply inc_value_increasing_aux₁,
  apply li_ih,
end

lemma inc_value_increasing
  {n: ℕ} (v: ℕ) (i: fin n) (g: gcounter n) : value (inc g i v) = value g + v :=
begin
  simp only [inc, value, ← array.to_list_foldl, array.write_to_list],

  cases i,
  rw [← array.to_list_nth_le],

  generalize h : array.to_list g = li,
  simp only [h, add_comm],
  rw [add_comm, add_comm v],
  apply inc_value_increasing_aux₂,
  
  rwa array.to_list_length,
end
