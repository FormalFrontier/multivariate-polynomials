# Credits and mathematical context

**Formal Frontier Agents** are the collective authors of the original project
formalization and documentation, licensed under [Apache-2.0](LICENSE). AI-assisted
agents developed mathematical arguments, Lean proofs, examples, guides and review
material. The individual contribution and review records remain in the project's
private owning records; mechanical transfers of previously developed proofs are
not independent proof authorship.

Atlas developed the library's interface direction and coordinated its releases;
Beacon contributed original mathematical expositions on block substitution and
finite-basis coordinates and coordinated much of the shared incubator-to-library
work; Anchor coordinated the fixed linear-division contribution and review.
Other agents made original project contributions to the ideal, homogeneous
evaluation, block substitution, iteration, degree, coefficient, division and
monic-lift results. These contributions and their transfers are distinguished
in the preserved project history; the collective authorship label does not
attribute third-party mathematics to this project.

## References and dependencies

- Ravi Vakil, *The Rising Sea: Foundations of Algebraic Geometry*, October 21,
  2025 draft, Exercise 6.7.E (PDF p. 199), motivates the variable-ideal theorem.
  This library does not formalize the complete short exact sequence. The
  [README](README.md) includes a finite-support argument.
- [Mathlib](https://github.com/leanprover-community/mathlib4) supplies the
  polynomial, ideal, homogeneity, substitution, monomial-order and linear-map
  infrastructure. Its finite-variable ideal theorem is not new here.
- Riccardo Brasca's mathlib theorem
  `Polynomial.lifts_and_natDegree_eq_and_monic` is a **univariate analogue**
  informing the distinct multivariate
  [lift](docs/monic-lift.md), not a pre-existing multivariate theorem.
- Antoine Chambert-Loir's mathlib `MonomialOrder` division infrastructure
  informs the [fixed linear-division](docs/linear-division.md) construction
  and the lift; native `Finsupp.linearCombination` and `coeffsIn` also remain
  contributions of mathlib's authors. This library's fixed, choice-dependent
  linear maps and its monic-lift theorem are separate project results.
- Project-authored mathematical expositions underlie the finite-support ideal,
  structural block laws and disjoint-block degree arguments. Their usable
  statements and limits appear in the linked [guides](docs/README.md); the
  expositions and source-specific correspondence are preserved separately.

No external source PDF, substantial book excerpt or third-party Lean proof is
distributed here. This credit does not assert a copyright holder for original
project files or transfer any third-party copyright.
