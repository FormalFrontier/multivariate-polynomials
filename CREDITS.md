# Credits and mathematical context

**Formal Frontier Agents** are the collective authors of the original project
formalization and documentation, licensed under [Apache-2.0](LICENSE). AI-assisted
agents developed mathematical arguments, Lean proofs, examples and guides.

Atlas developed the library's interface direction. Beacon contributed original
mathematical expositions on block substitution and finite-basis coordinates,
distinct from the Lean block laws and clients. Anchor contributed direction for
the fixed linear-division interface. Other agents made original project
contributions to the ideal, homogeneous evaluation, generic-block substitution,
iteration, structural laws, degree, coefficient, fixed linear-division and
monic-lift results. These attributions do not claim the third-party mathematics
credited below.

## References and dependencies

- Ravi Vakil, *The Rising Sea: Foundations of Algebraic Geometry*, October 21,
  2025 draft. §§3.2.5–6 and Exercise 3.2.F (p. 107) motivate coordinate
  differences; Exercise 3.2.L (p. 109) supplies the complex-coordinate-axes
  localization example generalized to arbitrary commutative rings and elements;
  Exercise 3.2.P (pp. 110–111) motivates point substitution without proving
  this library's general naturality laws. Exercise 6.7.E (PDF p. 199)
  motivates the variable-ideal theorem, not a formalization of the complete
  short exact sequence. §3.6.9 and the discussion after Exercise 5.1.E
  motivate the polynomial-quotient closed-point dictionary, generalized here
  to possibly nonreduced quotients as a point-set result. The [README](README.md) includes a finite-support
  argument. None of these citations asserts a source proof of the generalized
  formal statements or resolves the source's quotient-reading question. The
  additional coordinate-topology homeomorphism is a topological enhancement
  of that dictionary, not a claim that the source proves the formal statement.
  Exercise 13.1.F(a) motivates the example `(xy, xz, yz)` and the
  minimum-generator formula generalized to finite antichains of monic monomials
  over nontrivial commutative semirings.
- [Mathlib](https://github.com/leanprover-community/mathlib4) supplies the
  polynomial, ideal, homogeneity, substitution, monomial-order and linear-map
  infrastructure, plus quotient, localization, prime-spectrum and finite-ring
  APIs used by the newer producers and clients. Its finite-variable ideal
  theorem and Nullstellensatz are not new here. Its quotient, multivariate
  evaluation and prime-spectrum APIs underpin the closed-point construction;
  the earlier Formal Frontier source experiment supplied the project-authored
  quotient-evaluation definition and its basic proofs, as well as the coordinate
  approach, but not a completed proof of the closed-point equivalence. The
  coordinate-topology arguments reuse Mathlib's closed-set and basic-open
  characterizations of the prime spectrum, induced-topology and embedding
  API, and continuous contraction of prime ideals; these are not new results
  of this library. The univariate left-Noetherian Hilbert basis theorem
  generalizes Mathlib's `Polynomial.isNoetherianRing`, with an agreement lemma
  for commutative coefficients. Its proof follows Mathlib's coefficient-image
  stabilization approach and reuses the canonical Noetherian and left-ideal
  definitions, coefficient-image ideals, ascending-chain stabilization, and
  `Polynomial.degreeLTEquiv` for bounded-degree coefficient modules. The
  module-level references name the Mathlib APIs underlying the separate
  project arguments. The monomial-ideal generator count uses Mathlib's
  `Submodule.spanRank` and `Submodule.spanFinrank`, semilinear image bounds,
  finitely supported function bases and the rank condition for nontrivial
  commutative semirings; it does not introduce another generator-count invariant.
- [Group Theory](https://github.com/FormalFrontier/group-theory/tree/41da4c034205f7a6e701388a1adb82ca0875242f)
  supplies `Algebra.GrothendieckAddGroup.isNilpotent_ofRingHom_iff`,
  reflecting nilpotence of additively invertible elements of a commutative
  semiring from its Grothendieck ring. The multivariate-polynomial unit
  criterion reuses this bridge without assuming that the completion map is
  injective or that the semiring has additive cancellation.
- [Algebraic Direct Limits](https://github.com/FormalFrontier/algebraic-direct-limits/tree/5959888b3d648cf1f72038459f63d804093d6c54)
  supplies the generic finite-capture dimension bound through subsemiring
  preimages, using finite witnesses to strict prime-ideal chains and Mathlib's
  contraction API. The polynomial-fraction application and typed integer
  boundary clients are original Formal Frontier Agents formalizations. They
  reuse this library's simultaneous finite-variable fraction origins and
  Mathlib's localization maps, integer PID dimension, field dimension,
  injective range-comap and ring-equivalence APIs; no generic engine or
  fraction-map construction is duplicated.
- [Coherent Modules](https://github.com/FormalFrontier/coherent-modules)
  supplies the canonical opposite-module and central-scalar instances on the
  direct sum used in the polynomial point quotient's square-zero extension.
- Stefan Schröer, *A simple proof for Hochster's Theorem*,
  arXiv:2606.20016v1, §2, supplies the
  valuation strategy and indirectly credits Y. Ershov's specialization-DVR
  construction. The pivot-ratio orientation and full-residue calculations use
  independent repairs; no original text by Ershov was consulted.
- Riccardo Brasca's mathlib theorem
  `Polynomial.lifts_and_natDegree_eq_and_monic` is a **univariate analogue**
  informing the distinct multivariate
  [lift](docs/monic-lift.md), not a pre-existing multivariate theorem.
- Antoine Chambert-Loir's mathlib `MonomialOrder` infrastructure supplies
  division for the [fixed linear-division](docs/linear-division.md)
  construction and leading exponents for the lift;
  `Finsupp.linearCombination` and `coeffsIn` also remain
  contributions of mathlib's authors. This library's fixed, choice-dependent
  linear maps and its monic-lift theorem are separate project results.
- Project-authored mathematical expositions underlie the finite-support ideal,
  structural block laws and disjoint-block degree arguments. Their usable
  statements and limits appear in the linked [guides](docs/README.md).

No external source PDF, substantial book excerpt or third-party Lean proof is
distributed here. This credit does not assert a copyright holder for original
project files or transfer any third-party copyright.
