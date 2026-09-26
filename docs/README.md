# Generated API reference

[`API.md`](API.md) covers the one public non-finite-generation theorem, two
production modules and four private test/example modules. It retains the native
displayed signature, implicit hypotheses, original docstring and relative source
links. No JavaScript, fonts, remote styles, source PDF or dependency website ships.

## Reproduction

[`api-manifest.json`](api-manifest.json) identifies the exact analyzed Lean/config
inputs and native module records by full revision and SHA256. The final artifact
review binds those inputs, the manifest and generated output to its commit/tree.
Documentation-only changes do not alter mathematical inputs; source or pin changes
require fresh native generation and affected checks.

When the analyzed development commit exists, every source/config byte must match
its actual Git object. In an intentionally parentless release without that object,
the reproduced manifest must instead equal the release's committed manifest:
all nine source/config hashes, six native records, inventories, tool revision and
output hash. Every input must also equal the current committed file. Present wrong
objects, stale inputs and changed/uncommitted manifests are refused. This binds
inspected bytes, not provenance or proof checking; it does not promise development
history is available at GitHub. Use a committed checkout, not a plain no-Git export.

Build core-only doc-gen4 separately at
`97d4ecdfc8e09e7f511724c25e303d448de6a3db`, with its committed manifest and
Lean `v4.34.0-rc2`, using `lake build doc-gen4`. Do not change this library's
pins. Fetch its matching mathlib cache and compile all six modules using the
root README. Use fresh analysis/render directories and a full immutable analyzed
revision. Repeat `single` for all six modules in `scripts/generate_api.py`, using
the corresponding module source path. The native SQLite opener requires existing
directories:

```sh
mkdir /tmp/multivariate-analysis /tmp/multivariate-render
lake env /path/to/doc-gen4 single --build /tmp/multivariate-analysis MultivariatePolynomials.IdealOfVars api.db https://github.com/FormalFrontier/multivariate-polynomials/blob/FULL_SOURCE_COMMIT/MultivariatePolynomials/IdealOfVars.lean
lake env /path/to/doc-gen4 bibPrepass --build /tmp/multivariate-render --none
lake env /path/to/doc-gen4 fromDb --build /tmp/multivariate-render --manifest /tmp/multivariate-render/manifest.json /tmp/multivariate-analysis/api.db
python3 -B scripts/generate_api.py --native-data /tmp/multivariate-render/doc-data --source-revision FULL_SOURCE_COMMIT
python3 -B scripts/generate_api.py --native-data /tmp/multivariate-render/doc-data --source-revision FULL_SOURCE_COMMIT --check
python3 -B scripts/test_generate_api.py
```

Only Markdown and its manifest are distributed. Native source URIs bind the
analyzed revision; distributed links are checkout-relative. Intermediate HTML,
SQLite and assets are excluded, not implicitly cleared for redistribution.

## Checks and provenance

This purpose-specific adapter requires six native module records and exactly
`MvPolynomial.idealOfVars_not_fg` with theorem kind and the correct origin. It
retains every header token, normalizing whitespace only; module documentation
comes from each exact simple source module comment. Missing docstrings, malformed
markup, wrong kinds, unsafe/partial display, source/pin drift and invalid links
are refused. The adapter is not a Lean parser, native-run authenticator, proof
checker or release certificate. Data-only adverse controls do not replace actual
native receipts or independent mathematical and whole-artifact review.

Atlas adapted this renderer and controls from toric-ideals
`ab0c7d294a864deb3a6109aab30ebb77ebf5d2cb` (unaccepted when reused),
minimal-primes `bed9ea5b7d022529b6b9ee1888c81c3f02683aa6`, integral-closure
`bbc5da98d729c8737c7cef0df2f80c6323584b2e`, and ultimately Anchor's original
ideal-completion recipe `f0c8c34386109116e4912fb425a8ad15d9dc42a4`.
Collective credit, actual contributors and Apache-2.0 terms are retained;
approval is not transferred. Mathematical signatures/docstrings retain the
library's provenance. Lean, mathlib and doc-gen4 are separately credited tools
and dependencies, whose implementation and documentation are not copied here.
