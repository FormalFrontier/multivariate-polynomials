#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
# Authors: Formal Frontier Agents
# Historical six-module API adapter adapted by Atlas from earlier project
# adapters, including Anchor's documentation approach.
"""Bounded multivariate-polynomials Markdown adapter for native doc-gen4 records.

Retains complete displayed types, module comments, docstrings and relative source
links. This one-name adapter neither authenticates a native run nor checks proofs.
"""
import argparse
import hashlib
from html.parser import HTMLParser
import json
from pathlib import Path
import re
import subprocess
from urllib.parse import urlsplit

TOOL = '97d4ecdfc8e09e7f511724c25e303d448de6a3db'
MODULES = ('MultivariatePolynomials.IdealOfVars', 'MultivariatePolynomials',
           'Test.IdealOfVars', 'Test.Axioms', 'Test.LeafImport', 'Test.ReadmeExample')
INPUTS = tuple(m.replace('.', '/') + '.lean' for m in MODULES) + (
    'lean-toolchain', 'lakefile.toml', 'lake-manifest.json')
EXPECTED = {'MvPolynomial.idealOfVars_not_fg': ('theorem', MODULES[0])}
DISPLAY_KIND = {'MvPolynomial.idealOfVars_not_fg': 'theorem'}

def require(ok, reason):
    if not ok:
        raise ValueError(reason)

def digest(raw):
    return hashlib.sha256(raw).hexdigest()

class Header(HTMLParser):
    """Retain every native text token and implicit binder, normalizing only space."""
    def __init__(self, value):
        super().__init__(convert_charrefs=True)
        self.stack, self.text, self.kinds, self.names = [], [], [], []
        self.feed(value)
        self.close()
        require(not self.stack, 'unclosed native header')

    def handle_starttag(self, tag, attrs):
        require(tag in {'div', 'span', 'a'}, 'unexpected native header tag')
        attrs = dict(attrs)
        require(not any(k.startswith('on') for k in attrs), 'active header attribute')
        if tag == 'div' and 'decl_type' in attrs.get('class', '').split():
            self.text.append(' ')
        self.stack.append((tag, set(attrs.get('class', '').split())))

    def handle_endtag(self, tag):
        require(bool(self.stack) and self.stack[-1][0] == tag, 'unbalanced native header')
        self.stack.pop()

    def handle_data(self, value):
        require(bool(self.stack) or not value.strip(), 'text outside native header')
        self.text.append(value)
        if any('decl_kind' in c for _, c in self.stack):
            self.kinds.append(value)
        if any('decl_name' in c for _, c in self.stack):
            self.names.append(value)

    def handle_comment(self, _):
        raise ValueError('unexpected header comment')

    def handle_decl(self, _):
        raise ValueError('unexpected header declaration')

    def rendered(self):
        return ' '.join(''.join(self.text).split())

def module_doc(raw):
    # Every shipped module has exactly one plain, non-nested original-project
    # module doc. Refuse a different envelope instead of attempting a Lean parser.
    docs = re.findall(r'/-!(.*?)\-/', raw.decode(), re.S)
    require(len(docs) == 1 and '/-' not in docs[0], 'unsupported module-doc envelope')
    require('```' not in docs[0], 'unsupported module-doc fence')
    return docs[0].strip()

def render(records, revision, sources):
    require(re.fullmatch(r'[0-9a-f]{40}', revision) is not None, 'full source revision required')
    require(set(records) == set(MODULES), 'shipped module records differ')
    require(set(sources) == set(INPUTS), 'source/pin inventory differs')
    found, rows = {}, []
    for module in MODULES:
        record = records[module]
        require(record['name'] == module, 'native module name differs')
        for row in record['declarations']:
            info = row['info']
            name, kind = info['name'], info['kind']
            require(name in EXPECTED and EXPECTED[name] == (kind, module), 'unexpected public name/kind/module')
            require(name not in found, 'duplicate public declaration')
            path = module.replace('.', '/') + '.lean'
            link = urlsplit(info['sourceLink'])
            require(link.scheme == 'https' and link.netloc == 'github.com' and not link.query
                    and link.path == '/FormalFrontier/multivariate-polynomials/blob/' + revision + '/' + path,
                    'stale native source link')
            require(info['docLink'] == './' + module.replace('.', '/') + '.html#' + name, 'wrong native self link')
            require(type(info['line']) is int and 0 < info['line'] <= len(sources[path].splitlines()), 'invalid native source line')
            span = re.fullmatch(r'L([0-9]+)-L([0-9]+)', link.fragment)
            require(span is not None and int(span[1]) == info['line']
                    and info['line'] <= int(span[2]) <= len(sources[path].splitlines()),
                    'invalid native source range')
            header = Header(row['header'])
            require(''.join(header.names) == name and ''.join(header.kinds) == DISPLAY_KIND[name],
                    'header identity differs')
            text = header.rendered()
            require(bool(info['doc'].strip()), 'public docstring absent')
            require('```' not in text + info['doc'], 'unsupported Markdown fence')
            found[name] = (kind, module)
            rows.append(dict(name=name, kind=kind, header=text, doc=info['doc'].strip(),
                             path=path, line=info['line'], module=module))
    require(found == EXPECTED, 'missing public declaration')
    rows.sort(key=lambda r: (MODULES.index(r['module']), r['line']))
    lines = ['# Generated API reference', '',
        'Complete public API of multivariate-polynomials: one non-finite-generation theorem.',
        'Import `MultivariatePolynomials` or its direct ideal leaf. Four test modules contain',
        'private checked clients and the README example, not additional public API.', '',
        'Signatures below are native doc-gen4 display signatures with all displayed implicit',
        'arguments retained, not declarations with proof bodies. Short names use the source',
        'namespace and imports; universe parameters are arbitrary. Module documentation',
        'is extracted verbatim from the exact source. All source links are relative to this',
        'checkout. See [generation and provenance](README.md), [exact input manifest](api-manifest.json)',
        'and the [mathematical overview](../README.md).', '']
    for module in MODULES:
        path = module.replace('.', '/') + '.lean'
        lines += ['## Module `' + module + '`', '',
                  '\n'.join('> ' + s if s else '>' for s in module_doc(sources[path]).splitlines()), '',
                  '[Module source](../' + path + ')', '']
        for row in rows:
            if row['module'] != module:
                continue
            lines += ['### ' + row['name'], '', '```lean', row['header'], '```', '', row['doc'], '',
                      f"[Source](../{path}#L{row['line']}) (line {row['line']}).", '']
    markdown = '\n'.join(lines).encode()
    manifest = dict(format=1, generator='scripts/generate_api.py', docgen_revision=TOOL,
        analyzed_source_revision=revision, modules=list(MODULES),
        inputs={p: digest(sources[p]) for p in sorted(sources)},
        public_declarations=[r['name'] for r in rows],
        native_record_sha256={m: digest(json.dumps(records[m], sort_keys=True).encode()) for m in MODULES},
        api_sha256=digest(markdown), proof_certification=False)
    return markdown, (json.dumps(manifest, indent=2, sort_keys=True) + '\n').encode()

def bind_sources(root, revision, sources, generated_manifest):
    """Prefer real Git history; a parentless release can use its committed manifest.

    This binds the inspected inputs and native record bytes, not their provenance.
    A present but wrong Git object never activates the history-absent fallback.
    """
    require(re.fullmatch(r'[0-9a-f]{40}', revision) is not None, 'full source revision required')
    top = subprocess.check_output(['git', '--no-replace-objects', 'rev-parse', '--show-toplevel'], cwd=root).decode().strip()
    require(Path(top).resolve() == root.resolve(), 'generator must run in its own Git checkout')
    kind = subprocess.run(['git', '--no-replace-objects', 'cat-file', '--batch-check=%(objecttype)'], cwd=root,
        input=(revision + '\n').encode(), stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=True).stdout
    if kind == b'commit\n':
        for path, raw in sources.items():
            old = subprocess.check_output(['git', '--no-replace-objects', 'show', revision + ':' + path], cwd=root)
            require(old == raw, 'source/pin drift: ' + path)
        return 'git-object'
    require(kind == (revision + ' missing\n').encode(), 'selected Git object is not a commit')
    # The final release's own committed manifest is the authority when the
    # development object was intentionally omitted from its parentless ancestry.
    committed = subprocess.check_output(['git', '--no-replace-objects', 'show', 'HEAD:docs/api-manifest.json'], cwd=root)
    require((root / 'docs/api-manifest.json').read_bytes() == committed, 'uncommitted binding manifest')
    require(generated_manifest == committed, 'release manifest/source/native-record binding differs')
    for path, raw in sources.items():
        current = subprocess.check_output(['git', '--no-replace-objects', 'show', 'HEAD:' + path], cwd=root)
        require(current == raw, 'source/pin differs from release commit: ' + path)
    return 'committed-release-manifest'

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--native-data', required=True, type=Path)
    parser.add_argument('--source-revision', required=True)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    require(re.fullmatch(r'[0-9a-f]{40}', args.source_revision) is not None, 'full source revision required')
    root = Path(__file__).resolve().parent.parent
    sources = {p: (root / p).read_bytes() for p in INPUTS}
    records = {m: json.loads((args.native_data / ('declaration-data-' + m + '.bmp')).read_bytes()) for m in MODULES}
    api, manifest = render(records, args.source_revision, sources)
    binding = bind_sources(root, args.source_revision, sources, manifest)
    if not args.check:
        (root / 'docs').mkdir(parents=True, exist_ok=True)
    for name, raw in [('API.md', api), ('api-manifest.json', manifest)]:
        target = root / 'docs' / name
        if args.check:
            require(target.read_bytes() == raw, 'generated file differs: ' + name)
        else:
            target.write_bytes(raw)
    print(json.dumps(dict(status='matched' if args.check else 'generated', declarations=len(EXPECTED),
        api_sha256=digest(api), source_binding=binding, release_acceptance=False)))

if __name__ == '__main__':
    main()
