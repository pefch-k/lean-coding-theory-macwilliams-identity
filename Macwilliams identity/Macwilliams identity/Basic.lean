module
public import Mathlib
public import Mathlib.Data.Matrix.Basic
public import Mathlib.InformationTheory.Hamming
/-!
# MacWilliams Identity for Binary Linear Codes
This module formalizes the MacWilliams identity for linear codes over `ZMod 2`.
It includes the necessary definitions for the Hamming metric, inner products,
dual codes, and weight enumerator polynomials, culminating in the proof of
the binary MacWilliams identity.
-/

@[expose] public section
namespace InformationTheory
open scoped BigOperators
open Finset
open MvPolynomial

-- Define R as a Finite Field and n as a finite index set
variable {R : Type*} [Field R] [Fintype R] [DecidableEq R]
variable {n k : ℕ}
local notation "q" => Fintype.card R

/-! ### Base Definitions -/

/-- Type synonym for a Pi type equipped with the Hamming metric. -/
abbrev Word (R : Type*) (n : ℕ) : Type _ := Hamming (fun _ : Fin n ↦ R)

/-- A Linear Code is defined as a Submodule over the Word space. -/
abbrev LinearCode (R : Type*) [Field R] [Fintype R] [DecidableEq R] (n : ℕ) :=Submodule R (Word R n)
-- We use classical logic (`classical exact`) to bypass constructivist requirements for the subset.
noncomputable instance (C : LinearCode R n) : Fintype C := by
  classical exact Subtype.fintype (fun x => x ∈ C)

/-- The standard inner product form for Words over a finite field. -/
def innerProd : LinearMap.BilinForm R (Word R n) := LinearMap.mk₂ R
  (fun x y => ∑ i, x i * y i)
  (by
    intro x y z
    change (∑ i, (x i + y i) * z i) = (∑ i, x i * z i) + ∑ i, y i * z i
    simp only [add_mul,Finset.sum_add_distrib])
  (by
    intro c x y
    change (∑ i, (c * x i) * y i) = c * ∑ i, x i * y i
    simp_rw [mul_assoc, ← Finset.mul_sum])
  (by
    intro x y z
    change (∑ i, x i * (y i + z i)) = (∑ i, x i * y i) + ∑ i, x i * z i
    simp only [mul_add, Finset.sum_add_distrib])
  (by
    intro c x y
    change (∑ i, x i * (c * y i)) = c * ∑ i, x i * y i
    simp only [mul_left_comm, Finset.mul_sum])

omit [Fintype R] [DecidableEq R] in
/-- The inner product is symmetric. -/
lemma innerProd_symm (y z : Word R n) : innerProd y z = innerProd z y := by
  change ∑ i, y i * z i = ∑ i, z i * y i
  simp_rw [mul_comm]

/-- The dual code is the orthogonal complement with respect to the inner product.
It consists of all vectors that are orthogonal to every vector in C. -/
def dualCode (C : LinearCode R n) : LinearCode R n := LinearMap.BilinForm.orthogonal innerProd C

-- Custom notations to align the Lean code with standard coding theory literature
scoped notation:100 C "^⊥" => dualCode C
scoped notation "‖" x "‖ₕ" => hammingNorm x
scoped notation "⟪" x "," y "⟫" => innerProd x y

/-- The weight enumerator polynomial of a linear code.
it depends on 'Polynomial.semiring', which is 'noncomputable' -/
noncomputable def weightEnumerator (C : LinearCode R n) : Polynomial ℚ :=
  ∑ c : C, Polynomial.X ^ (‖c.val‖ₕ)

scoped notation "W_[" C "]" => weightEnumerator C

noncomputable instance (C : LinearCode R n) : Fintype (C^⊥) := by
  classical exact Subtype.fintype (fun x => x ∈ C^⊥)

noncomputable instance (C : LinearCode R n) : DecidablePred (fun x => x ∈ C) :=
  fun x => Classical.propDecidable (x ∈ C)


namespace LinearCode

noncomputable abbrev dim (C : LinearCode R n) : ℕ := Module.finrank R C

/-! ### Helper Lemmas for the MacWilliams Identity -/
/-- The cardinality of a linear code relates to its dimension. -/
lemma card (C : LinearCode R n) : Fintype.card C = q ^ dim C := by
  exact Module.card_eq_pow_finrank

/-- Cancels an element in `ZMod 2` when added to itself. -/
lemma add_add_cancel_zmod_two (w v : ZMod 2) : w + v + v = w := by
  fin_cases v <;> fin_cases w <;> rfl

/-- Exponentiation rule for `-1` over the finite field `ZMod 2`. Δειχνουμε πρακτικα πως για καθε
ισχυειγια καθε συνδιασμο επιλογων -/
lemma pow_add_eq_pow_mul_pow_zmod_two (A B : ZMod 2) :
    (-1 : ℚ) ^ ZMod.val (A + B) = (-1 : ℚ) ^ ZMod.val A * (-1 : ℚ) ^ ZMod.val B := by
     fin_cases A <;> fin_cases B
     · -- 0 + 0 = 0
      change (-1 : ℚ) ^ 0 = (-1 : ℚ) ^ 0 * (-1 : ℚ) ^ 0; norm_num
     · -- 0 + 1 = 1
      change (-1 : ℚ) ^ 1 = (-1 : ℚ) ^ 0 * (-1 : ℚ) ^ 1; norm_num
     · -- 1 + 0 = 1
      change (-1 : ℚ) ^ 1 = (-1 : ℚ) ^ 1 * (-1 : ℚ) ^ 0; norm_num
     · -- 1 + 1 = 0
      change (-1 : ℚ) ^ 0 = (-1 : ℚ) ^ 1 * (-1 : ℚ) ^ 1; norm_num

/- Generalizes the exponentiation rule for `-1` over a `Finset` sum ||(-1)^(Σ a_i) = Π (-1)^(a_i)-/
lemma pow_sum_eq_prod_pow (y z : Word (ZMod 2) n) (s : Finset (Fin n)) :
    (-1 : ℚ) ^ ZMod.val (∑ i ∈ s, z i * y i) = ∏ i ∈ s, (-1 : ℚ) ^ ZMod.val (z i * y i) := by
  induction s using Finset.induction_on
  · simp only [Finset.sum_empty, ZMod.val_zero, pow_zero, Finset.prod_empty]
  · rename_i a_elem s_set ha_not_in ih_hyp
    rw [Finset.sum_insert ha_not_in, Finset.prod_insert ha_not_in,
    pow_add_eq_pow_mul_pow_zmod_two (z a_elem * y a_elem) (∑ i ∈ s_set, z i * y i),ih_hyp]
lemma pow_dim_ne_zero {C : LinearCode R n} : (2:ℚ)^(dim C) ≠ 0 := by positivity
/--
Transforms an exponentiation over `ZMod 2` into an `if-then-else` expression.
Since `v ∈ ZMod 2` can only be `0` or `1`, `x^v` is `1` if `v = 0` and `x` if `v ≠ 0`.
-/
lemma pow_eq_ite_zmod_two (x : ℚ) (v : ZMod 2) : x ^ ZMod.val v = if v ≠ 0 then x else 1 := by
  -- We split the if-statement into two cases based on the condition v ≠ 0
  split_ifs with h
  · -- Case: v ≠ 0. In ZMod 2, the only non-zero element is 1.
    have hv_eq_one : ZMod.val v = 1 := by
      fin_cases v
      · contradiction
      · rfl
    rw [hv_eq_one, pow_one]
  · -- Case: v = 0 (since the condition v ≠ 0 is false).
    have hv_eq_zero : ZMod.val v = 0 := by
      push Not at h
      rw [h, ZMod.val_zero]
    rw [hv_eq_zero, pow_zero]

/-! ### Main Theorems -/
/--
Evaluates the sum of characters over a linear code.
If `y` is in the dual code, the sum is `2^dim`. Otherwise, it is `0`.
-/
--lemma 1
lemma sum_pow_innerProd_eq (C : LinearCode (ZMod 2) n) (y : Word (ZMod 2) n) :
    ∑ z : C, (-1:ℚ)^(ZMod.val ⟪z.val, y⟫) = if y ∈ C^⊥ then (2:ℚ)^(dim C) else 0 := by
  split_ifs with h9
  · -- Case: y ∈ C^⊥.
    have hy_ortho : ∀ z : C, ⟪z.val, y⟫ = 0 := by
      intro z
      simp only [dualCode, LinearMap.BilinForm.orthogonal] at h9
      exact h9 z.val z.prop
    simp_rw [hy_ortho, ZMod.val_zero, pow_zero]
    simp [Finset.sum_const, Finset.card_univ, card]
  · -- Case: y ∉ C^⊥
    obtain ⟨u, hu_mem, hu⟩ : ∃ u ∈ C, ⟪u, y⟫ = 1 := by
      by_contra hy_in_dual_contra
      push Not at hy_in_dual_contra
      apply h9
      simp only [dualCode, LinearMap.BilinForm.orthogonal]
      intro z hz
      have h_innerProd_ne_one : ⟪z, y⟫ ≠ 1 := hy_in_dual_contra z hz
      generalize ⟪z, y⟫ = v at h_innerProd_ne_one ⊢
      fin_cases v
      · rfl
      · contradiction
    -- Define a variable change (bijection) over C via translation by u.
    let α : C ≃ C := {
      toFun    := fun z => ⟨z.val + u, C.add_mem z.prop hu_mem⟩,
      invFun   := fun z => ⟨z.val + u, C.add_mem z.prop hu_mem⟩,
      left_inv := fun z => Subtype.ext (by
       funext i
       simp only [add_assoc]
       have h_zero : z.val i + u i + u i = z.val i := add_add_cancel_zmod_two (z.val i) (u i)
       simp only [<-Pi.add_apply] at h_zero
       rw [add_assoc] at h_zero
       rw[<- h_zero]
       rfl),
      right_inv := fun z => Subtype.ext (by
       funext i
       simp only [ add_assoc]
       --μια φορα που χρησιμοποιω το αντ αντ
       have h_zero : z.val i + u i + u i = z.val i := add_add_cancel_zmod_two (z.val i) (u i)
       simp only[<-Pi.add_apply] at h_zero
       rw [add_assoc] at h_zero
       rw[<- h_zero]
       rfl)
    }
    -- Applying the bijection leaves the total sum invariant.
    have sum_comp_equiv : ∑ z : C, (-1:ℚ)^(ZMod.val ⟪(α z).val, y⟫) =
                          ∑ z : C, (-1:ℚ)^(ZMod.val ⟪z.val, y⟫) := by
      exact Equiv.sum_comp α (fun z => (-1:ℚ)^(ZMod.val ⟪z.val, y⟫))
    -- However, translating by u flips the sign of every term.
    have sum_eq_neg_sum : ∑ z : C, (-1:ℚ)^(ZMod.val ⟪(α z).val, y⟫) =
                          - ∑ z : C, (-1:ℚ)^(ZMod.val ⟪z.val, y⟫) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro z _
      have h_inner : ⟪(α z).val, y⟫ = ⟪z.val, y⟫ + 1 := by
        change ⟪z.val + u, y⟫ = ⟪z.val, y⟫ + 1
        rw [innerProd.add_left, hu]
      rw [h_inner]
      generalize innerProd z.val y = v
      fin_cases v <;> rfl
    rw [sum_eq_neg_sum] at sum_comp_equiv
    exact eq_zero_of_neg_eq sum_comp_equiv --η λιγοτερα αμεσο linarith

/--
Evaluates the inner summation of the MacWilliams identity over the vector space.
Transforms the sum into a product form using character properties.
-/
--lemma 2
lemma sum_mul_pow_innerProd_eq (x : ℚ) (z : Word (ZMod 2) n) :
    ∑ y : Word (ZMod 2) n, (x^(‖y‖ₕ))*(-1:ℚ)^(ZMod.val ⟪z, y⟫) = ((1-x)^‖z‖ₕ)*(1+x)^(n-‖z‖ₕ) := by
  calc
  ∑ y : Word (ZMod 2) n, (x^‖y‖ₕ)*(-1:ℚ)^(ZMod.val ⟪z, y⟫)
  _= ∑ y : Word (ZMod 2) n, ∏ i : Fin n, (x^(ZMod.val (y i)) * (-1:ℚ)^(ZMod.val (z i * y i))) := by
    unfold hammingNorm innerProd
    congr
    ext y
    simp only [Finset.prod_mul_distrib, LinearMap.mk₂_apply]
    congr 1
    --x_1 στοιχεια της λεξης
    · have h_ite : (∏ x_1 : Fin n, x ^ ZMod.val (y x_1)) =
                     ∏ x_1 : Fin n, if y x_1 ≠ 0 then x else 1 := by
       apply Finset.prod_congr rfl
       intro i _
       exact pow_eq_ite_zmod_two x (y i)
      simp only [h_ite,Finset.prod_ite,Finset.prod_const_one, mul_one, Finset.prod_const]
    · exact pow_sum_eq_prod_pow y z Finset.univ
  _= ∏ i : Fin n, ∑ j : ZMod 2, (x^(ZMod.val j) * (-1:ℚ)^(ZMod.val (z i * j))) := by
    exact (Fintype.prod_sum (fun (i : Fin n) (j : ZMod 2) =>
      x ^ ZMod.val j * (-1:ℚ) ^ ZMod.val (z i * j))).symm
  _= ∏ i : Fin n, if z i = 0 then (1 + x) else (1 - x) := by
    apply Finset.prod_congr rfl
    intro i _
    have univ_zmod_two : (Finset.univ : Finset (ZMod 2)) = {0, 1} := rfl
    rw [univ_zmod_two, Finset.sum_insert, Finset.sum_singleton]
    swap
    · decide
    split_ifs with hz
    · rw [hz]
      simp only [mul_zero, ZMod.val_zero, pow_zero, mul_one, ZMod.val_one, pow_one]
    · have hz1 : z i = 1 := by
       generalize z i = v at hz ⊢
       fin_cases v <;> simp only [Nat.reduceAdd, Fin.zero_eta, Fin.isValue]
       · contradiction
       · rfl
      rw [hz1]
      simp only [mul_zero, ZMod.val_zero, pow_zero, mul_one, ZMod.val_one, pow_one]
      ring
  _ = (1-x)^(‖z‖ₕ) * (1+x)^(n - ‖z‖ₕ) := by
    rw [Finset.prod_ite]
    simp only [Finset.prod_const]
    rw [mul_comm]
    unfold hammingNorm
    congr
    have card_add_card_not :=
    --|{x∈S|P(x)}|+|{x∈S|¬P(x)}=|S|
    Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun x => z x = 0)--(X)(P(X))
    simp only [card_univ, Fintype.card_fin] at card_add_card_not
    exact Nat.eq_sub_of_add_eq card_add_card_not

/--
The MacWilliams Identity for Binary Linear Codes.
Relates the weight enumerator polynomial of a linear code to the weight enumerator of its dual.
-/
theorem macwilliams_identity_binary (C : LinearCode (ZMod 2) n) (x : ℚ) (hx : x ≠ -1) :
    (weightEnumerator (C^⊥)).eval x = (1/((2:ℚ)^(dim C)))*((1+x)^n)*(W_[C]).eval ((1-x)/(1+x)) := by
  -- Define the core character sum function used to bridge the primal and dual spaces
  let sum_weight_char {C : LinearCode (ZMod 2) n} (x : ℚ) : ℚ :=
    ∑ z : C, ∑ y : Word (ZMod 2) n, x^‖y‖ₕ * (-1:ℚ)^(ZMod.val ⟪z.val, y⟫)
  have h_add_one_ne_zero : (1 + x) ≠ 0 := by intro h; exact hx (by linarith)
  -- Step 1: Relate the character sum to the primal code C
  have sum_eq_primal : sum_weight_char x = ((1+x)^n) * (W_[C]).eval ((1-x)/(1+x)) := calc
    sum_weight_char x
      = ∑ z : C, ∑ y : Word (ZMod 2) n, x ^ ‖y‖ₕ * (-1:ℚ) ^ (ZMod.val ⟪z.val, y⟫) := rfl
    _ = ∑ z : C, (1-x) ^ ‖z.val‖ₕ * (1+x) ^ (n - ‖z.val‖ₕ) := by
      apply Finset.sum_congr rfl
      intro z _
      exact sum_mul_pow_innerProd_eq x z.val
    _ = ((1+x)^n) * ∑ z : C, (1-x) ^ ‖z.val‖ₕ / ((1+x) ^ (‖z.val‖ₕ : ℕ)) := by
      rw [Finset.mul_sum]
      apply Fintype.sum_congr
      intro z
      have norm_le_n : ‖z.val‖ₕ ≤ n := by
        simpa [Fintype.card_fin] using hammingNorm_le_card_fintype (ι := Fin n) (x := z.val)
      rw [pow_sub₀ _ h_add_one_ne_zero norm_le_n]
      ring
    _ = ((1+x)^n) * ∑ z : C, (((1-x)/(1+x))^‖z.val‖ₕ) := by
      congr 1
      apply Finset.sum_congr rfl
      intro z _
      simp [div_pow]
    _ = ((1+x)^n) * (W_[C]).eval ((1-x)/(1+x)) := by
      congr 1
      simp only [weightEnumerator,Polynomial.eval_finsetSum,Polynomial.eval_pow, Polynomial.eval_X]
  -- Step 2: Relate the character sum to the dual code C^⊥ 2o calc
  have sum_eq_dual : sum_weight_char x = ((2:ℚ)^(dim C)) * W_[C^⊥].eval x := calc
    sum_weight_char x
      = ∑ z : C, ∑ y : Word (ZMod 2) n, x ^ ‖y‖ₕ * (-1:ℚ) ^ (ZMod.val ⟪z.val, y⟫) := rfl
    _ = ∑ y : Word (ZMod 2) n, ∑ z : C, x ^ ‖y‖ₕ * (-1:ℚ) ^ (ZMod.val ⟪z.val, y⟫) := by
     rw [Finset.sum_comm]
    _ = ∑ y : Word (ZMod 2) n, ((x ^ ‖y‖ₕ) * ∑ z : C, (-1:ℚ) ^ (ZMod.val ⟪z.val, y⟫)) := by
     simp only [← Finset.mul_sum]
    _ = ∑ y : Word (ZMod 2) n, x ^ ‖y‖ₕ * (if y ∈ (C^⊥) then (2:ℚ)^(dim C) else 0) := by
      apply Finset.sum_congr rfl
      intro y _
      rw [sum_pow_innerProd_eq]
    _ = ∑ y : Word (ZMod 2) n, if y ∈ C^⊥ then x ^ ‖y‖ₕ * (2:ℚ)^(dim C) else 0 := by
      simp only [mul_ite, mul_zero]
    _ = ∑ y : C^⊥, (x ^ ‖y.val‖ₕ) * (2:ℚ)^(dim C) := by
      rw [← Finset.sum_filter]
      symm
      apply Finset.sum_bij (fun a _ => a.val)
      · intro a _
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact a.2
      · intro a ha k hk
        exact Subtype.ext
      · intro a1 h_a1
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h_a1
        exact ⟨⟨a1, h_a1⟩, Finset.mem_univ _, rfl⟩
      · intro a ha
        rfl
    _ = ((2:ℚ)^(dim C)) * ∑ y : C^⊥, (x ^ ‖y.val‖ₕ) := by
      simp_rw [mul_comm _ ((2:ℚ)^(dim C)),Finset.mul_sum]
    _ = (2:ℚ)^(dim C) * (weightEnumerator (C^⊥)).eval x := by
      congr 1
      simp only [weightEnumerator,Polynomial.eval_finsetSum, Polynomial.eval_pow, Polynomial.eval_X]
  -- Step 3: Combine primal and dual relations to solve for the dual weight enumerator
  calc
    W_[C^⊥].eval x
      = 1/2^(dim C) * (2^(dim C) * W_[C^⊥].eval x) := by field_simp [pow_dim_ne_zero]
    _ = 1/2^(dim C) * ((1+x)^n * (W_[C]).eval ((1-x)/(1+x))) := by rw [← sum_eq_primal, sum_eq_dual]
    _ = 1/2^(dim C) * (1+x)^n * (W_[C]).eval ((1-x)/(1+x)) := by ring

end LinearCode

/-! ### Concrete Examples (Sanity Checks) -/
section
def u : Word (ZMod 2) 7 := ![1, 1, 1, 1, 0, 0, 0]
def v : Word (ZMod 2) 7 := ![0, 0, 0, 0, 1, 1, 1]
def l : Word (ZMod 2) 7 := ![1, 1, 1, 1, 1, 1, 1]
def l1 : ZMod 2 := v 4
def l3 : ZMod 2 := v 3
def G : Fin 2 → Word (ZMod 2) 7 := ![u, v]
lemma gen_indep : LinearIndependent (ZMod 2) G := by rw [Fintype.linearIndependent_iff]; decide
def C : LinearCode (ZMod 2) 7 := Submodule.span (ZMod 2) (Set.range G)

#eval l1
#eval l3
#check 2 • v
#check u+v
#eval u+l
#eval 3•v
#eval ‖v‖-- *mistake* that is not hamming norm
#eval ‖v‖ₕ
#eval ⟪u,v⟫
#eval ⟪v,l⟫
#eval ⟪u,u⟫ --παραδειγμα οπου το εσωτερικου με τον ευατο δινει το 0-νικο
example (ha : u ∈ C) (hb : v ∈ C) : u + v ∈ C := by exact C.add_mem ha hb
#check u+l=v
universe u v
def p2 :=
  ∀ {α : Type u} {β : Type v} (R : α → β → Prop),
    (∃ x : α, ∀ y : β, R x y) → (∀ y : β, ∃ x : α, R x y)
#check  (∀ (α : Type 1), α → α)
#check p2
#check List (Type)
#check @id
#check @id (Nat)
#check @id (String)
#eval @id (Nat) (5)
#eval@id (String) ("hello")
inductive Nat where
  | zero : Nat
  | succ (n : Nat) : Nat
end
end InformationTheory
