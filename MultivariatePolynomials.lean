/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import MultivariatePolynomials.IdealOfVars
public import MultivariatePolynomials.HomogeneousEvaluation
public import MultivariatePolynomials.BlockSubstitution
public import MultivariatePolynomials.IteratedBlockSubstitution

/-!
# Multivariate polynomials

Public aggregate import for the variable-ideal non-finite-generation theorem,
homogeneous-polynomial evaluation scaling laws, and disjoint-block polynomial
substitution and its evaluation and zero-locus laws, including finite iteration
through tuple-indexed disjoint blocks. Import the corresponding
`MultivariatePolynomials.IdealOfVars`,
`MultivariatePolynomials.HomogeneousEvaluation`, or
`MultivariatePolynomials.BlockSubstitution` or
`MultivariatePolynomials.IteratedBlockSubstitution` leaf directly when only one
is needed. Test modules are deliberately not re-exported.
-/
