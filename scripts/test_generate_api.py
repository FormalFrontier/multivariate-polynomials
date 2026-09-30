# SPDX-License-Identifier: Apache-2.0
# Authors: Formal Frontier Agents
# Historical six-module adapter tests adapted by Atlas from earlier project
# adapters, including Anchor's documentation approach.
"""Data-only adapter controls; they do not authenticate native Lean records."""
import copy
import json
from pathlib import Path
import subprocess
import tempfile
import unittest
import generate_api as api

REV = 'a' * 40

def fixture():
    records = {m: dict(name=m, declarations=[]) for m in api.MODULES}
    for i, (name, (kind, module)) in enumerate(api.EXPECTED.items(), 1):
        assumptions = '(k : Type u) (σ : Type v) [CommSemiring k] [Nontrivial k] [Infinite σ]'
        header = (f'<div><span class="decl_kind">{api.DISPLAY_KIND[name]}</span> '
                  f'<span class="decl_name">{name}</span> <span>{assumptions}</span> :'
                  '<div class="decl_type">¬ (idealOfVars σ k).FG</div></div>')
        path = module.replace('.', '/')
        records[module]['declarations'].append(dict(header=header, info=dict(name=name,
            kind=kind, doc='Synthetic test data, not a Lean theorem.', line=i,
            sourceLink='https://github.com/FormalFrontier/multivariate-polynomials/blob/' + REV + '/' + path + f'.lean#L{i}-L{i+1}',
            docLink='./' + path + '.html#' + name)))
    sources = {p: b'/-! Synthetic module documentation. -/\n' + b'fixture\n' * 100 for p in api.INPUTS}
    return records, sources

class Controls(unittest.TestCase):
    def test_complete_inventory_and_binding(self):
        records, sources = fixture()
        raw, manifest = api.render(records, REV, sources)
        facts = json.loads(manifest)
        self.assertEqual(len(facts['public_declarations']), 1)
        self.assertEqual(raw.count(b'## Module'), 6)
        self.assertEqual(facts['api_sha256'], api.digest(raw))
        self.assertEqual(set(facts['inputs']), set(api.INPUTS))
        self.assertNotIn(b'example.invalid', raw + manifest)
        self.assertFalse(facts['proof_certification'])

    def test_preserve_text_and_entities(self):
        self.assertEqual(api.Header('<div><span>{A : Type u}</span> :'
            '<div class="decl_type">x &lt; y ∧ x ≤ y</div></div>').rendered(),
            '{A : Type u} : x < y ∧ x ≤ y')
        self.assertEqual(api.Header('<span><span>Algebra</span>.<span>TensorProduct</span></span>').rendered(),
            'Algebra.TensorProduct')

    def test_theorem_kind_and_full_binders_preserved(self):
        records, sources = fixture()
        raw, _ = api.render(records, REV, sources)
        self.assertIn(b'theorem MvPolynomial.idealOfVars_not_fg', raw)
        self.assertIn('(k : Type u) (σ : Type v) [CommSemiring k] [Nontrivial k] [Infinite σ]'.encode(), raw)
        for kind in ['def', 'axiom', 'unsafe def', 'partial def']:
            altered = copy.deepcopy(records)
            row = altered[api.MODULES[0]]['declarations'][0]
            row['header'] = row['header'].replace('theorem', kind)
            with self.assertRaises(ValueError):
                api.render(altered, REV, sources)

    def test_refuse_corrupt_records(self):
        mutations = [lambda r: r.pop(api.MODULES[2]),
            lambda r: r[api.MODULES[0]]['declarations'].pop(),
            lambda r: r[api.MODULES[0]]['declarations'].append(copy.deepcopy(r[api.MODULES[0]]['declarations'][0])),
            lambda r: r[api.MODULES[2]]['declarations'].append(copy.deepcopy(r[api.MODULES[0]]['declarations'][0])),
            lambda r: r[api.MODULES[0]].update(name='Wrong')]
        for key, value in [('name', 'Wrong'), ('kind', 'axiom'), ('doc', ''),
                           ('line', 0), ('line', True), ('line', 999),
                           ('sourceLink', 'moving/main'), ('docLink', 'wrong'), ('doc', '```')]:
            mutations.append(lambda r, k=key, v=value: r[api.MODULES[0]]['declarations'][0]['info'].update({k: v}))
        mutations += [lambda r: r[api.MODULES[0]]['declarations'][0].update(header='<script>bad</script>'),
            lambda r: r[api.MODULES[0]]['declarations'][0].update(header='<div><span></div>'),
            lambda r: r[api.MODULES[0]]['declarations'][0].update(header='<span onclick="x">bad</span>')]
        for i, mutation in enumerate(mutations):
            with self.subTest(control=i):
                records, sources = fixture()
                mutation(records)
                with self.assertRaises(ValueError):
                    api.render(records, REV, sources)

    def test_revision_inventory_module_docs(self):
        records, sources = fixture()
        for rev in ['main', 'a' * 39, '-' * 40]:
            with self.assertRaises(ValueError):
                api.render(records, rev, sources)
        for source in [b'', b'/-! one -/\n/-! two -/', b'/-! outer /- inner -/ -/']:
            with self.assertRaises(ValueError):
                api.module_doc(source)
        sources.pop('lean-toolchain')
        with self.assertRaises(ValueError):
            api.render(records, REV, sources)

    def test_native_github_ranges(self):
        for suffix in ['', '#L0-L1', '#L2-L3', '#L1-L999', '#L1-L0', '#L1-L2?query']:
            records, sources = fixture()
            row = records[api.MODULES[0]]['declarations'][0]['info']
            row['sourceLink'] = row['sourceLink'].split('#')[0] + suffix
            with self.assertRaises(ValueError):
                api.render(records, REV, sources)

    def test_parentless_committed_manifest_binding(self):
        records, sources = fixture()
        raw, manifest = api.render(records, REV, sources)
        with tempfile.TemporaryDirectory(prefix='multivariate-doc-binding-') as directory:
            root = Path(directory)
            def git(*args):
                return subprocess.check_output(['git', '-c', 'user.name=Test',
                    '-c', 'user.email=test@example.invalid', *args], cwd=root, stderr=subprocess.PIPE)
            git('init', '-q')
            for path, value in sources.items():
                (root / path).parent.mkdir(parents=True, exist_ok=True)
                (root / path).write_bytes(value)
            (root / 'docs').mkdir()
            (root / 'docs/api-manifest.json').write_bytes(manifest)
            (root / 'docs/API.md').write_bytes(raw)
            git('add', '.')
            git('commit', '-qm', 'Synthetic parentless documentation fixture')
            head = git('rev-parse', 'HEAD').decode().strip()
            self.assertEqual(api.bind_sources(root, REV, sources, manifest), 'committed-release-manifest')
            self.assertEqual(api.bind_sources(root, head, sources, manifest), 'git-object')
            for changed in [manifest + b' ', manifest.replace(REV.encode(), b'b' * 40)]:
                with self.assertRaises(ValueError):
                    api.bind_sources(root, REV, sources, changed)
            with self.assertRaises(ValueError):
                api.bind_sources(root, 'b' * 40, sources, manifest.replace(REV.encode(), b'b' * 40))
            blob = git('rev-parse', 'HEAD:docs/API.md').decode().strip()
            with self.assertRaises(ValueError):
                api.bind_sources(root, blob, sources, manifest)
            (root / 'docs/api-manifest.json').write_bytes(manifest + b' ')
            with self.assertRaises(ValueError):
                api.bind_sources(root, REV, sources, manifest)
            (root / 'docs/api-manifest.json').write_bytes(manifest)
            altered = dict(sources)
            altered[api.INPUTS[0]] += b'changed\n'
            for revision in [head, REV]:
                with self.assertRaises(ValueError):
                    api.bind_sources(root, revision, altered, manifest)
            # An existing commit missing an input is not treated as absent history.
            git('rm', '--', api.INPUTS[0])
            git('commit', '-qm', 'Synthetic missing input')
            missing = git('rev-parse', 'HEAD').decode().strip()
            with self.assertRaises(subprocess.CalledProcessError):
                api.bind_sources(root, missing, sources, manifest)

if __name__ == '__main__':
    unittest.main()
