/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import MultivariatePolynomials.IdealOfVars
public import MultivariatePolynomials.HomogeneousEvaluation
public import MultivariatePolynomials.BlockSubstitution
public import MultivariatePolynomials.IteratedBlockSubstitution
public import MultivariatePolynomials.BlockSubstitutionLaws
public import MultivariatePolynomials.BlockSubstitutionDegree
public import MultivariatePolynomials.PolynomialCoefficientHomogeneity
public import MultivariatePolynomials.LinearCoefficientEvaluation

/-!
# Multivariate polynomials

Public aggregate import for the variable-ideal non-finite-generation theorem,
homogeneous-polynomial evaluation scaling laws, and disjoint-block polynomial
substitution and its evaluation and zero-locus laws, including exact total degree
under no-zero-divisors coefficients and finite iteration
through tuple-indexed disjoint blocks and structural laws for renaming,
associativity, units and concatenation of iteration words. Extracting a polynomial
parameter coefficient via native interchange preserves each homogeneous label.
An arbitrary coefficient-linear map commutes with evaluation at base-semiring-valued
points via the native additive coefficient map, without a multiplicativity premise.
Import the corresponding
`MultivariatePolynomials.IdealOfVars`,
`MultivariatePolynomials.HomogeneousEvaluation`, or
`MultivariatePolynomials.BlockSubstitution`,
`MultivariatePolynomials.IteratedBlockSubstitution` or
`MultivariatePolynomials.BlockSubstitutionLaws` or
`MultivariatePolynomials.BlockSubstitutionDegree` or
`MultivariatePolynomials.PolynomialCoefficientHomogeneity` or
`MultivariatePolynomials.LinearCoefficientEvaluation` leaf directly when only one
is needed. Test modules are deliberately not re-exported.
-/
