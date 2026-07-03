# lean-coding-theory-macwilliams-identity
## Overview:
This project formalizes the concept of dual code, and their Weight Enumerator polynomials, culminating in the formal verification of the **MacWilliams Identity** for codes over `ZMod 2`. 

The motivation behind the MacWilliams Identity is that computing the weight distribution (the number of codewords of each possible weight) of a linear code is computationally expensive, growing exponentially with the code's dimension `k`. The MacWilliams Identity provides a powerful algebraic bridge: it proves that the weight enumerator of a code `C` completely determines the weight enumerator of its orthogonal dual code `C^⊥`. 

                                 W_C^⊥(x) = 1/|C| * (1+x)^n * W_C((1-x)/(1+x))

This implies that if `C^⊥` has a much smaller dimension than `C`, we can easily compute the weight enumerator of `C^⊥` and use this identity to instantly find the weight enumerator of `C`, drastically reducing the computational complexity. 


## Design choices:
* Base Field `ZMod 2`: I restricted the formalization to binary codes (`ZMod 2`) for this project. This allowed me to map the finite field elements directly to the rational numbers using the formula `(-1)^(val x)`, bypassing the need to implement general abstract character theory (additive characters over `F_q`) which would add significant overhead.
 
* `LinearCode`: This is defined as a `Submodule` of the `Word` space (a Pi type equipped with the Hamming metric). To bridge the gap between classical mathematics and Lean's constructivism, I instantiated `Fintype` and `DecidablePred` for linear codes using `open Classical`, allowing seamless finite sum evaluations without requiring constructive algorithms for set membership.

* `weightEnumerator`: I defined it as a standard univariate `Polynomial ℚ`. The identity is then stated using the `.eval` function with the explicit condition `x ≠ -1`, which significantly simplifies the algebraic rewriting processes in Lean.

* `dualCode`: Defined cleanly as the orthogonal complement of `C` using `LinearMap.BilinForm.orthogonal` applied to the standard dot product.

## Main Theorems:
* Lemma `sum_pow_innerProd_eq`: Evaluates the sum of characters `(-1)^⟪z, y⟫` over a linear code `C`. It proves that if `y ∈ C^⊥`, the sum equals `2^(dim C)`, and if `y ∉ C^⊥`, the sum perfectly cancels out to `0`.

* Lemma `sum_mul_pow_innerProd_eq`: A vector space expansion lemma that evaluates the inner summation of the MacWilliams identity, transforming the sum over the entire space into a product form `(1-x)^‖z‖ * (1+x)^(n-‖z‖)` using character properties.

* Theorem `macwilliams_identity_binary`: The main identity relating `W_[C^⊥].eval x` to `(W_[C]).eval ((1-x)/(1+x))`.

## Proof strategies:
* Lemma `sum_pow_innerProd_eq`: For the case where `y ∉ C^⊥`, we use proof by contradiction to show there exists an element `u ∈ C` such that `⟪u, y⟫ = 1`. We then define a bijective translation (`Equiv`) on the code `z ↦ z + u`. Applying this bijection leaves the total sum invariant (`Equiv.sum_comp`), but mathematically it flips the sign of every term, proving that the sum must equal its own negative (hence, it is `0`).

* Theorem `macwilliams_identity_binary`: We define a double summation (the core character sum) that acts as a bridge. We evaluate this double summation in two different ways (swapping the order of summation via `Finset.sum_comm`). 
    - The first evaluation (using `sum_mul_pow_innerProd_eq`) yields the primal expression `(1+x)^n * W_C(...)`.
    - The second evaluation (using `sum_pow_innerProd_eq` and filtering the set) yields the dual expression `2^(dim C) * W_C^⊥(x)`.
Finally, a `calc` block and the `ring` tactic are used to equate the two and solve for `W_C^⊥(x)`.


## Note:
I would like to eventually generalize this formalization to arbitrary finite fields `F_q` using Mathlib's Additive Characters, and potentially adapt it to use Homogeneous Polynomials (`MvPolynomial`) to perfectly match the standard Mathlib conventions.
