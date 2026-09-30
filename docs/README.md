# API documentation and historical snapshot

[`API.md`](API.md) is the current **hand-maintained** public module/result map:
ten producer modules (including the aggregate), twelve registered
test/example modules and thirty-eight selected public declarations across
twenty-two Lean modules. It is neither
freshly native-generated nor a proof certificate. The separate
[homogeneous-evaluation guide](homogeneous-polynomial-evaluation.md) explains
the two scaling laws and their assumptions; the
[block-substitution guide](block-substitution.md) covers generic blocks, while
the [finite-iteration guide](iterated-block-substitution.md) explains the
separate tuple-indexed iterator and its conditional degree powers. The
[structural-law guide](block-substitution-laws.md) covers associative, unit,
renaming and finite-word concatenation laws over arbitrary commutative semirings.
The [exact-degree guide](block-substitution-degree.md) describes the new
no-zero-divisors theorem, its arbitrary-input boundary cases and direct-import
client; it is not part of the archived native snapshot.
The [polynomial-coefficient-homogeneity guide](polynomial-coefficient-homogeneity.md)
explains the homogeneous-label preservation theorem, finite-parameter client,
and weight-zero limitation; this added leaf is likewise not part of the
archived native snapshot.
The [linear-coefficient-evaluation guide](linear-coefficient-evaluation.md)
explains the base-valued point and linear (not multiplicative) coefficient-map
assumptions, ordinary-import clients and its revision-specific lifecycle;
this new leaf is also absent from the archived native snapshot.

The [fixed linear-division guide](linear-division.md) describes chosen linear
quotient and remainder maps, componentwise leading-cone avoidance, coefficient
ideal preservation, ordinary-import clients and the limits of noncanonical choice.
This new leaf is likewise absent from the archived native snapshot.

[`API-initial-snapshot.md`](API-initial-snapshot.md) is byte-for-byte the
original six-module native doc-gen4 output: one public ideal theorem, two
producer modules and four private test/example modules. The unchanged
[`api-manifest.json`](api-manifest.json) records its analyzed source revision
`35e72ff648fc5d73ffa4232ed2b1971cb61891fd`, six native module records,
input hashes and `api_sha256` of **that archived snapshot**
(`3683ee0fa8ecdaf34f72317b6c89388834a22a42364d008d6edb40c9ac05b0df`),
not the current `API.md`. Its old root/lakefile source hashes, module count and
inventory must not be interpreted as validation of the changed library. Its
relative source links show matching original line positions only in the original
six-module checkout.
The two unchanged [`generate_api.py`](../scripts/generate_api.py) and
[`test_generate_api.py`](../scripts/test_generate_api.py) scripts are scoped
only to the old native snapshot. Data-only fixture tests of the old adapter do
not check the current API, proofs or this promotion.

## Reproducing only the original six-module output

Use a separate checkout at the exact original official release
`1caf2e85e7b8d9d9a15f47e96ffd60fbb51d5fda` (same tree as the destination's
original main `5581825d52b8ef6efe393d18c9232ecbd5d2ac5e`), or at the exact
unmodified analyzed-input revision
`35e72ff648fc5d73ffa4232ed2b1971cb61891fd`. Do **not** run the old
adapter's output/check mode on the expanded current checkout: its hard-coded
six-module inventory and original input hashes cannot describe twenty-two modules.
Use a committed checkout, not a plain no-Git export; the original contract
requires the actual Git object or the original manifest with byte-identical
current inputs in an intentionally parentless release.

Build core-only doc-gen4 separately at
`97d4ecdfc8e09e7f511724c25e303d448de6a3db`, with its committed manifest
and Lean `v4.34.0-rc2`. Do not change this library's pins. Fetch matching
precompiled mathlib caches for each mathlib-dependent build, then compile the
six original project modules using the historical README in that checkout.
Use fresh analysis/render directories and the full immutable analyzed revision.
Repeat `single` for all six modules in the historical
`scripts/generate_api.py` inventory, using the corresponding source paths.
The native SQLite opener requires existing directories:

```sh
mkdir /tmp/multivariate-analysis /tmp/multivariate-render
lake env /path/to/doc-gen4 single --build /tmp/multivariate-analysis MultivariatePolynomials.IdealOfVars api.db https://github.com/FormalFrontier/multivariate-polynomials/blob/FULL_SOURCE_COMMIT/MultivariatePolynomials/IdealOfVars.lean
lake env /path/to/doc-gen4 bibPrepass --build /tmp/multivariate-render --none
lake env /path/to/doc-gen4 fromDb --build /tmp/multivariate-render --manifest /tmp/multivariate-render/manifest.json /tmp/multivariate-analysis/api.db
python3 -B scripts/generate_api.py --native-data /tmp/multivariate-render/doc-data --source-revision FULL_SOURCE_COMMIT
python3 -B scripts/generate_api.py --native-data /tmp/multivariate-render/doc-data --source-revision FULL_SOURCE_COMMIT --check
python3 -B scripts/test_generate_api.py
```

This is historical reproduction guidance, not an instruction to regenerate
current `API.md` or evidence of a new native run. Only Markdown and the manifest
were distributed from that workflow; intermediate HTML, SQLite and assets were
excluded, not implicitly cleared for redistribution. The historical adapter
requires exactly `MvPolynomial.idealOfVars_not_fg` and six module records with
theorem kind/origin; it retains native header tokens and module comments with
bounded normalization and checks input/link drift. It is not a Lean parser,
native-run authenticator, proof checker or release certificate. Old data-only
adverse controls do not replace actual native receipts, mathematical review or
whole-artifact review of a new revision.

Atlas adapted the historical renderer and controls from toric-ideals
`ab0c7d294a864deb3a6109aab30ebb77ebf5d2cb` (unaccepted when reused),
minimal-primes `bed9ea5b7d022529b6b9ee1888c81c3f02683aa6`, integral-closure
`bbc5da98d729c8737c7cef0df2f80c6323584b2e`, and ultimately Anchor's
ideal-completion recipe `f0c8c34386109116e4912fb425a8ad15d9dc42a4`.
Collective credit, actual contributors and Apache-2.0 terms are retained;
approval is not transferred. Lean, mathlib and doc-gen4 are separately credited
tools and dependencies; their implementations and documentation are not copied.
