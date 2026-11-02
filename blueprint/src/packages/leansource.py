"""
Local plasTeX package: leansource

Problem this fixes
-------------------
leanblueprint's `blueprint` package renders every `\\lean{...}` node as a
link to `{dochome}/find/#doc/{name}`, defaulting `dochome` to
`https://leanprover-community.github.io/mathlib4_docs`. That is correct for
declarations that live in Mathlib, but every declaration in *this* project
lives in the Hironaka library, not Mathlib, so every such link 404s.
Setting `\\dochome` would only change the base URL, and this project has no
doc-gen4 site of its own to point it at.

Instead, this package shows the actual Lean source of each declaration,
read directly from the files in this repository, in place of the link.

How it works
------------
LeanArchitect already writes a `% at FILE:LINE.COL-LINE.COL` comment into
every generated blueprint artifact file under
`.lake/build/blueprint/module/**/*.artifacts/*.tex` (see
`Architect/Output.lean`, `NodeWithPos.toLatex`), recording exactly where the
corresponding Lean declaration lives. This package rescans those comments
(a plain text pass, independent of the plasTeX/TeX parse of the *.tex
content itself, since TeX comments are not visible to plasTeX macros), and
slices the named line/column range out of the referenced `.lean` file.

It must be loaded (via `\\usepackage{leansource}` in web.tex) *after*
leanblueprint's own `\\usepackage[...]{blueprint}`, since it overwrites two
template lists that package populates: `thm_header_hidden_extras_tpl` (the
"L∃∀N" modal button on each node) and `dep_graph`'s `extra_modal_links_tpl`
(the "Lean" tooltip on dependency-graph node popups). The unrelated GitHub
discussion-link templates in those same lists are left untouched.

Known limitations
------------------
* LeanArchitect only records one file/position per blueprint *label*: the
  first Lean declaration tagged with that label. A label whose `\\lean{a,b}`
  lists several merged declarations (e.g. a `to_additive` pair, or two
  `@[blueprint "same-label"]` tags) therefore only gets a snippet for the
  first name; later names are listed with no snippet rather than a broken
  link. In this project that affects a small minority of nodes.
* The comment reflects whichever `.lean` source was on disk the last time
  `lake build :blueprint` ran. If the source has since changed, the line/
  column range can point at the wrong text (or fail to slice at all, which
  is handled gracefully). Re-run `lake build :blueprint` before
  `leanblueprint web` to refresh it.
"""
import html
import re
from pathlib import Path
from typing import Optional

from jinja2 import Template

from leanblueprint.Packages.blueprint import (
    LEAN_DECLS_TPL,
    LEAN_LINKS_TPL,
    GITHUB_ISSUE_TPL,
    GITHUB_LINK_TPL,
)

_POS_RE = re.compile(r'^% at (.+):(\d+)\.(\d+)-(\d+)\.(\d+)\s*$', re.MULTILINE)
_LEAN_RE = re.compile(r'^\\lean\{([^}]*)\}\s*$', re.MULTILINE)

Position = tuple  # (Path, int, int, int, int) = (file, l1, c1, l2, c2)


def _collect_lean_positions(build_module_dir: Path) -> dict:
    """Map each Lean declaration name to the (file, l1, c1, l2, c2) position
    LeanArchitect recorded for it, by rescanning the `% at ...` comments in
    every generated artifact file."""
    positions: dict = {}
    if not build_module_dir.is_dir():
        return positions
    for texfile in build_module_dir.glob('**/*.artifacts/*.tex'):
        try:
            text = texfile.read_text(encoding='utf-8')
        except OSError:
            continue
        lean_m = _LEAN_RE.search(text)
        pos_m = _POS_RE.search(text)
        if not lean_m or not pos_m:
            continue
        names = [n.strip() for n in lean_m.group(1).split(',') if n.strip()]
        if not names:
            continue
        file_str, l1, c1, l2, c2 = pos_m.groups()
        # Only the first tagged declaration of a merged label has a
        # position; don't let a later file overwrite an earlier find.
        positions.setdefault(
            names[0], (Path(file_str), int(l1), int(c1), int(l2), int(c2)))
    return positions


_source_cache: dict = {}


def _read_snippet(pos: Optional[Position]) -> Optional[str]:
    """Slice the Lean source named by `pos` (1-indexed line, 0-indexed
    column, end-exclusive, matching Lean's `Position`/`String.Range`
    convention) out of its file. Returns None if anything is out of range
    (typically: stale position from before a source edit)."""
    if pos is None:
        return None
    file_path, l1, c1, l2, c2 = pos
    key = str(file_path)
    lines = _source_cache.get(key)
    if lines is None:
        try:
            lines = file_path.read_text(encoding='utf-8').split('\n')
        except OSError:
            lines = []
        _source_cache[key] = lines
    if not lines or l1 < 1 or l2 > len(lines) or l1 > l2:
        return None
    try:
        if l1 == l2:
            return lines[l1 - 1][c1:c2]
        first = lines[l1 - 1][c1:]
        middle = lines[l1:l2 - 1]
        last = lines[l2 - 1][:c2]
        return '\n'.join([first] + middle + [last])
    except IndexError:
        return None


# Replacement for LEAN_DECLS_TPL: the "L∃∀N" modal button's content.
LEAN_SOURCE_DECLS_TPL = Template("""
    {% if obj.userdata.leandecls %}
    <button class="modal lean">L∃∀N</button>
    {% call modal('Lean source') %}
        <ul class="uses lean_source_list">
          {% for lean, source in obj.userdata.lean_sources %}
          <li>
            <div class="lean_decl_name">{{ lean }}</div>
            {% if source %}
            <pre class="lean_source"><code>{{ source }}</code></pre>
            {% else %}
            <span class="lean_source_missing">(source not available; re-run &lsquo;lake build :blueprint&rsquo;)</span>
            {% endif %}
          </li>
          {% endfor %}
        </ul>
    {% endcall %}
    {% endif %}
""")

# Replacement for LEAN_LINKS_TPL: the dependency-graph node popup's "Lean" entry.
LEAN_SOURCE_LINKS_TPL = Template("""
  {% if thm.userdata['lean_sources'] -%}
  <div class="tooltip lean_tooltip">
      <span class="lean_link">Lean</span>
      <ul class="tooltip_list lean_source_list">
        {% for name, source in thm.userdata['lean_sources'] %}
        <li>
          <div class="lean_decl_name">{{ name }}</div>
          {% if source %}
          <pre class="lean_source"><code>{{ source }}</code></pre>
          {% else %}
          <span class="lean_source_missing">(source not available)</span>
          {% endif %}
        </li>
        {% endfor %}
      </ul>
  </div>
  {%- endif %}
""")


def ProcessOptions(options, document):
    """Called when `\\usepackage{leansource}` is processed. Must run after
    leanblueprint's `\\usepackage[...]{blueprint}` in the same document."""
    working_dir = Path(document.userdata.get('working-dir', '.'))
    # plastex is invoked with blueprint/src as cwd (see leanblueprint's
    # `mk_web`), so the Lake build directory is two levels up.
    build_module_dir = (
        working_dir / '..' / '..' / '.lake' / 'build' / 'blueprint' / 'module'
    ).resolve()
    positions = _collect_lean_positions(build_module_dir)

    def make_lean_sources() -> None:
        """Populate node.userdata['lean_sources'] = [(name, escaped_snippet_or_None), ...]
        for every node in every dependency graph, replacing the Mathlib-doc
        `lean_urls` that leanblueprint's own `make_lean_data` computed."""
        for graph in document.userdata['dep_graph']['graphs'].values():
            for node in graph.nodes:
                leandecls = node.userdata.get('leandecls', [])
                sources = []
                for name in leandecls:
                    snippet = _read_snippet(positions.get(name))
                    escaped = html.escape(snippet) if snippet is not None else None
                    sources.append((html.escape(name), escaped))
                node.userdata['lean_sources'] = sources

    # leanblueprint's own `make_lean_data` (which builds `leandecls` per
    # node from `\lean{...}` and the dependency graphs themselves) runs at
    # priority 150; run after it.
    document.addPostParseCallbacks(160, make_lean_sources)

    # Swap the two Mathlib-doc-link templates for source-snippet versions,
    # in place, leaving the unrelated GitHub-discussion-link templates.
    hidden_extras = document.userdata.setdefault('thm_header_hidden_extras_tpl', [])
    hidden_extras[:] = [
        LEAN_SOURCE_DECLS_TPL if tpl is LEAN_DECLS_TPL else tpl
        for tpl in hidden_extras
    ]

    modal_links = document.userdata['dep_graph'].setdefault('extra_modal_links_tpl', [])
    modal_links[:] = [
        LEAN_SOURCE_LINKS_TPL if tpl is LEAN_LINKS_TPL else tpl
        for tpl in modal_links
    ]

    # Keep references reachable (avoids "unused import" confusion; these
    # two are matched by identity above but never otherwise referenced).
    _ = (GITHUB_ISSUE_TPL, GITHUB_LINK_TPL)
