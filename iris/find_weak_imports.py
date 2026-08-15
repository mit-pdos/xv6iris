#!/usr/bin/env python3
"""Find local Rocq imports that use only a small, self-contained file fragment.

The dead-import checker answers whether an import can disappear.  This tool
answers the next question: when an import is live, does the importing file use
only a few declarations whose dependencies *inside the imported file* are also
few?  Such an edge is a candidate for moving those declarations to a smaller
module and importing that module instead.

The analysis uses the `.glob` files emitted by a successful build:

* references in the importing file identify the declarations used directly;
* byte offsets assign references in the imported file to the declaration whose
  statement/proof contains them; and
* following those intra-file references gives the explicit internal closure.

Records/inductives and their generated projections/constructors/schemes count
as one declaration unit because they cannot usefully be factored separately.
The result is deliberately only a report.  `.glob` does not expose every use
through tactics, hint databases, notation side effects, or typeclass search, so
the reported closure is a lower bound that a developer must validate while
doing the refactor.

By default an edge is weak when its explicit transitive closure contains at
most 10% of the imported file's declaration units.  This is the only candidate
threshold; direct-root and absolute-closure counts are reported as context but
do not affect eligibility.  An otherwise-weak edge is then omitted when the
imported module is already a transitive dependency of another direct import in
the consumer: that explicit edge adds no serialization to the Require DAG.
Dependencies on `KernelDecode*.v` are also omitted as an expected generated
decode-layer pattern.

Usage:
  python3 find_weak_imports.py --dir .
  python3 find_weak_imports.py --dir . --report weak-imports.md
  python3 find_weak_imports.py --dir . --files ProofCopyin.v ProofCopyout.v
  python3 find_weak_imports.py --dir . --max-fraction .05
  python3 find_weak_imports.py --dir . --top 0       # show every candidate
  python3 find_weak_imports.py --dir . --format json
"""
from __future__ import annotations

import argparse
import bisect
import fnmatch
import json
import os
import re
from dataclasses import dataclass, field

# Share logical-name resolution and the content-digest freshness check with the
# nightly dead-import checker.  This analyzer uses a read-only Require parser
# below because it must also see multiline statements and statements followed
# by comments; the dead-import checker's editing parser intentionally operates
# one source line at a time.
from detect_unused_imports import (
    ImportStmt,
    glob_status,
    local_prefix_for_dir,
    logical_path,
)


REF_RE = re.compile(
    r"^R(\d+):(\d+)\s+(\S+)\s+(\S+)\s+(\S+)\s+(\S+)\s*$"
)
DECL_RE = re.compile(r"^([a-z]+)\s+(\d+):(\d+)\s+(\S+)\s+(\S+)\s*$")

# These glob declarations represent units that can plausibly move.  `rec` is
# used for records as well as recursive definitions by Rocq's glob format.
UNIT_KINDS = {
    "prf", "def", "rec", "inst", "ind", "ax", "abbrev", "not",
    "class", "coe",
}
GENERATED_KINDS = {"constr", "proj", "scheme"}
CONTROL_KINDS = {"sec", "mod", "modtype", "var"}
EXPECTED_PRODUCER_PATTERNS = ("KernelDecode*.v",)

REQUIRE_RE = re.compile(
    r"""(?mx)
        ^[ \t]*
        (?:From[ \t]+(?P<from>[\w.]+)[ \t]+)?
        Require[ \t\r\n]+
        (?P<mode>Import[ \t\r\n]+|Export[ \t\r\n]+)?
        (?P<mods>
            [\w']+(?:\.[\w']+)*
            (?:[ \t\r\n]+[\w']+(?:\.[\w']+)*)*
        )
        [ \t\r\n]*\.
    """
)


def _mask_coq_comments_and_strings(text: str) -> str:
    """Replace comments/strings with spaces while preserving offsets/newlines."""
    masked = list(text)
    depth = 0
    in_string = False
    i = 0

    def blank(index: int) -> None:
        if masked[index] not in "\r\n":
            masked[index] = " "

    while i < len(text):
        if in_string:
            blank(i)
            if text[i] == '"':
                # Rocq escapes a quote inside a string by doubling it.
                if i + 1 < len(text) and text[i + 1] == '"':
                    blank(i + 1)
                    i += 2
                    continue
                in_string = False
            i += 1
            continue

        if text[i] == '"':
            blank(i)
            in_string = True
            i += 1
            continue

        if i + 1 < len(text) and text[i:i + 2] == "(*":
            blank(i)
            blank(i + 1)
            depth += 1
            i += 2
            continue
        if depth and i + 1 < len(text) and text[i:i + 2] == "*)":
            blank(i)
            blank(i + 1)
            depth -= 1
            i += 2
            continue
        if depth:
            blank(i)
        i += 1
    return "".join(masked)


def parse_complete_imports(text: str) -> list[ImportStmt]:
    """Parse read-only Require statements, including comments and newlines."""
    masked = _mask_coq_comments_and_strings(text)
    statements: list[ImportStmt] = []
    for match in REQUIRE_RE.finditer(masked):
        mode = (match.group("mode") or "").strip()
        kind = {"Import": "import", "Export": "export", "": "require"}[mode]
        statements.append(
            ImportStmt(
                lineno=text.count("\n", 0, match.start()) + 1,
                raw=text[match.start():match.end()],
                kind=kind,
                from_prefix=match.group("from"),
                modules=match.group("mods").split(),
            )
        )
    return statements


@dataclass(frozen=True)
class GlobRef:
    start: int
    module: str
    secpath: str
    name: str
    kind: str


@dataclass
class DeclUnit:
    index: int
    secpath: str
    name: str
    kind: str
    start: int
    line: int
    aliases: set[tuple[str, str]] = field(default_factory=set)
    deps: set[int] = field(default_factory=set)
    referenced_modules: set[str] = field(default_factory=set)

    @property
    def label(self) -> str:
        if self.secpath == "<>":
            return self.name
        return f"{self.secpath}.{self.name}"


@dataclass
class ModuleInfo:
    vfile: str
    logical_name: str
    lines: int
    units: list[DeclUnit]
    refs: list[GlobRef]
    alias_to_unit: dict[tuple[str, str], int]


@dataclass
class Candidate:
    consumer: str
    producer: str
    import_line: int
    import_kind: str
    producer_lines: int
    producer_units: int
    direct_units: list[str]
    direct_symbols: list[str]
    closure_units: list[str]
    local_prerequisites: list[str]

    @property
    def direct_count(self) -> int:
        return len(self.direct_units)

    @property
    def closure_count(self) -> int:
        return len(self.closure_units)

    @property
    def fraction(self) -> float:
        return self.closure_count / self.producer_units

    @property
    def avoided_units(self) -> int:
        return self.producer_units - self.closure_count

    def as_dict(self) -> dict[str, object]:
        return {
            "consumer": self.consumer,
            "producer": self.producer,
            "import_line": self.import_line,
            "import_kind": self.import_kind,
            "direct_count": self.direct_count,
            "direct_units": self.direct_units,
            "direct_symbols": self.direct_symbols,
            "closure_count": self.closure_count,
            "closure_units": self.closure_units,
            "producer_units": self.producer_units,
            "producer_lines": self.producer_lines,
            "fraction": self.fraction,
            "avoided_units": self.avoided_units,
            "local_prerequisites": self.local_prerequisites,
        }


@dataclass(frozen=True)
class EdgeWeakness:
    """Weakness measurement for one explicit local import edge.

    The key used by :class:`Analysis` is ``(consumer, producer)`` with both
    names expressed as source basenames without ``.v``.  This is also the name
    form used by ``.CoqMakefile.d`` and lets the build profiler consume these
    measurements without duplicating the glob analysis.
    """

    consumer: str
    producer: str
    status: str
    direct_count: int | None = None
    closure_count: int | None = None
    producer_units: int | None = None
    unmatched_symbols: int = 0
    direct_symbols: tuple[str, ...] = ()

    @property
    def fraction(self) -> float | None:
        if self.closure_count is None or not self.producer_units:
            return None
        return self.closure_count / self.producer_units

    def annotation(self) -> str:
        if self.status == "no_symbols":
            return "n/a — no explicit declaration refs"
        if self.status == "unmapped":
            return f"unknown — {self.unmatched_symbols} unmapped ref(s)"
        if self.fraction is None:
            return "unknown"
        ratio = (
            f"{self.fraction:.1%} "
            f"({self.closure_count}/{self.producer_units})"
        )
        symbols = ", ".join(f"`{name}`" for name in self.direct_symbols)
        symbol_suffix = f"; symbols: {symbols}" if symbols else ""
        if self.status == "weak":
            return f"weak — {ratio}{symbol_suffix}"
        if self.status == "covered":
            return (
                f"weak ratio — {ratio}; already transitive{symbol_suffix}"
            )
        if self.status == "expected":
            return (
                f"weak ratio — {ratio}; expected decode edge{symbol_suffix}"
            )
        return f"not weak — {ratio}"


@dataclass
class Analysis:
    candidates: list[Candidate]
    project_files: int
    usable_files: int
    import_edges: int
    live_symbol_edges: int
    skipped_files: dict[str, str]
    unmatched_symbols: int
    transitively_covered_edges: int
    expected_producer_edges: int
    edge_weaknesses: dict[tuple[str, str], EdgeWeakness]


def _line_starts(path: str) -> list[int]:
    try:
        with open(path, "rb") as source:
            data = source.read()
    except OSError:
        return [0]
    starts = [0]
    starts.extend(i + 1 for i, byte in enumerate(data) if byte == 0x0A)
    return starts


def _line_of(starts: list[int], offset: int) -> int:
    return bisect.bisect_right(starts, offset)


def _display_symbol(secpath: str, name: str) -> str:
    return name if secpath == "<>" else f"{secpath}.{name}"


def is_expected_producer(vfile: str) -> bool:
    return any(
        fnmatch.fnmatchcase(vfile, pattern)
        for pattern in EXPECTED_PRODUCER_PATTERNS
    )


def parse_module(vpath: str, glob_path: str) -> ModuleInfo:
    """Parse one source/glob pair and build its declaration dependency graph."""
    logical_name = ""
    raw_decls: list[tuple[str, int, int, str, str]] = []
    refs: list[GlobRef] = []
    with open(glob_path, errors="replace") as f:
        for sequence, line in enumerate(f):
            line = line.rstrip("\n")
            if line.startswith("F"):
                logical_name = line[1:]
                continue
            match = REF_RE.match(line)
            if match:
                start, _end, module, secpath, name, kind = match.groups()
                if kind != "lib" and name != "<>":
                    refs.append(
                        GlobRef(int(start), module, secpath, name, kind)
                    )
                continue
            match = DECL_RE.match(line)
            if match:
                kind, start, _end, secpath, name = match.groups()
                raw_decls.append((kind, int(start), sequence, secpath, name))

    if not logical_name:
        raise ValueError(f"{glob_path}: no F<logical-module> record")

    starts = _line_starts(vpath)
    # Put a real unit before generated aliases at the same source offset.
    raw_decls.sort(
        key=lambda row: (row[1], 0 if row[0] in UNIT_KINDS else 1, row[2])
    )

    units: list[DeclUnit] = []
    alias_to_unit: dict[tuple[str, str], int] = {}
    # An anchor changes which declaration owns subsequent references.  Context,
    # Section, and Module commands deliberately anchor to None so their setup
    # references are not charged to the previous declaration.
    anchors_at: dict[int, int | None] = {}
    current: int | None = None

    for kind, offset, _sequence, secpath, name in raw_decls:
        owner: int | None
        if kind in UNIT_KINDS:
            owner = len(units)
            unit = DeclUnit(
                owner, secpath, name, kind, offset, _line_of(starts, offset)
            )
            unit.aliases.add((secpath, name))
            units.append(unit)
            current = owner
        elif kind in GENERATED_KINDS:
            attach = False
            if current is not None:
                parent_kind = units[current].kind
                attach = (
                    (kind == "constr" and parent_kind in {"ind", "rec", "class"})
                    or (kind == "proj" and parent_kind in {"rec", "class"})
                    or (kind == "scheme" and parent_kind == "ind")
                )
            if attach:
                owner = current
                units[owner].aliases.add((secpath, name))
            else:
                # Rare standalone generated declarations remain visible to the
                # analysis instead of making a real consumer reference vanish.
                owner = len(units)
                unit = DeclUnit(
                    owner, secpath, name, kind, offset, _line_of(starts, offset)
                )
                unit.aliases.add((secpath, name))
                units.append(unit)
                current = owner
        elif kind in CONTROL_KINDS:
            owner = None
            current = None
        else:
            # `binder` records occur inside a declaration and must not break its
            # ownership interval.  Unknown kinds get the same safe treatment.
            continue
        anchors_at[offset] = owner

    for unit in units:
        for alias in unit.aliases:
            alias_to_unit[alias] = unit.index

    anchor_offsets = sorted(anchors_at)
    for ref in refs:
        pos = bisect.bisect_right(anchor_offsets, ref.start) - 1
        if pos < 0:
            continue
        owner = anchors_at[anchor_offsets[pos]]
        if owner is None:
            continue
        units[owner].referenced_modules.add(ref.module)
        if ref.module == logical_name:
            key = (ref.secpath, ref.name)
            dependency = alias_to_unit.get(key)
            # Rocq does not always emit a declaration record for a record's
            # constructor.  It does emit a self-reference when a following
            # [Arguments MkFoo ...] command names it; while that command is
            # still in the record's ownership interval, recover the constructor
            # as another alias of that indivisible record unit.
            if (
                dependency is None
                and ref.kind == "constr"
                and units[owner].kind in {"ind", "rec", "class"}
            ):
                units[owner].aliases.add(key)
                alias_to_unit[key] = owner
                dependency = owner
            if dependency is not None and dependency != owner:
                units[owner].deps.add(dependency)

    try:
        with open(vpath, errors="replace") as source:
            source_lines = len(source.read().splitlines())
    except OSError:
        source_lines = 0
    return ModuleInfo(
        os.path.basename(vpath), logical_name, source_lines, units, refs,
        alias_to_unit,
    )


def project_vfiles(dir_path: str) -> list[str]:
    """Files listed in `_CoqProject`, falling back to all sibling `.v` files."""
    coqproject = os.path.join(dir_path, "_CoqProject")
    if not os.path.isfile(coqproject):
        return sorted(f for f in os.listdir(dir_path) if f.endswith(".v"))
    files: list[str] = []
    with open(coqproject) as f:
        for line in f:
            line = line.split("#", 1)[0].strip()
            if not line or line.startswith("-"):
                continue
            for token in line.split():
                if token.endswith(".v"):
                    files.append(os.path.basename(token))
    return sorted(dict.fromkeys(files))


def local_import_graph(
    dir_path: str, vfiles: list[str], prefix: str
) -> dict[str, set[str]]:
    """Direct local `Require` graph, including Import, Export, and bare edges.

    Candidate reporting may exclude `Require Export`, but exports still load
    their targets and therefore must participate when deciding whether some
    *other* explicit import adds a new serialization edge.
    """
    names = {
        (f"{prefix}.{vfile[:-2]}" if prefix else vfile[:-2])
        for vfile in vfiles
    }
    graph: dict[str, set[str]] = {name: set() for name in names}
    for vfile in vfiles:
        consumer = f"{prefix}.{vfile[:-2]}" if prefix else vfile[:-2]
        try:
            with open(os.path.join(dir_path, vfile), errors="replace") as source:
                text = source.read()
        except OSError:
            continue
        for stmt in parse_complete_imports(text):
            for token in stmt.modules:
                dependency = logical_path(stmt, token, prefix)
                if dependency in names and dependency != consumer:
                    graph[consumer].add(dependency)
    return graph


def transitive_imports(
    graph: dict[str, set[str]], start: str,
    cache: dict[str, frozenset[str]],
) -> frozenset[str]:
    """All modules reachable from `start`, cycle-safe and cached per start."""
    if start in cache:
        return cache[start]
    seen: set[str] = set()
    work = list(graph.get(start, ()))
    while work:
        module = work.pop()
        if module in seen:
            continue
        seen.add(module)
        work.extend(graph.get(module, ()))
    result = frozenset(seen)
    cache[start] = result
    return result


def _closure(info: ModuleInfo, roots: set[int]) -> set[int]:
    seen = set(roots)
    work = list(roots)
    while work:
        unit = work.pop()
        for dependency in info.units[unit].deps:
            if dependency not in seen:
                seen.add(dependency)
                work.append(dependency)
    return seen


def analyze(
    dir_path: str,
    *,
    files: list[str] | None = None,
    max_fraction: float = 0.10,
    include_export: bool = False,
    allow_stale: bool = False,
) -> Analysis:
    dir_path = os.path.abspath(dir_path)
    prefix = local_prefix_for_dir(dir_path)
    all_vfiles = project_vfiles(dir_path)
    import_graph = local_import_graph(dir_path, all_vfiles, prefix)
    import_closure_cache: dict[str, frozenset[str]] = {}
    selected = set(files) if files else None
    infos: dict[str, ModuleInfo] = {}
    skipped: dict[str, str] = {}

    for vfile in all_vfiles:
        vpath = os.path.join(dir_path, vfile)
        gpath = os.path.join(dir_path, vfile[:-2] + ".glob")
        state = glob_status(dir_path, vfile)
        if state != "fresh" and not (state == "stale" and allow_stale):
            skipped[vfile] = state
            continue
        try:
            info = parse_module(vpath, gpath)
        except (OSError, ValueError) as error:
            skipped[vfile] = str(error)
            continue
        infos[info.logical_name] = info

    candidates: list[Candidate] = []
    import_edges = 0
    live_symbol_edges = 0
    unmatched_symbols = 0
    transitively_covered_edges = 0
    expected_producer_edges = 0
    edge_weaknesses: dict[tuple[str, str], EdgeWeakness] = {}
    seen_edges: set[tuple[str, str]] = set()

    for consumer in sorted(infos.values(), key=lambda info: info.vfile):
        if selected is not None and consumer.vfile not in selected:
            continue
        try:
            with open(os.path.join(dir_path, consumer.vfile),
                      errors="replace") as source:
                text = source.read()
        except OSError:
            continue
        for stmt in parse_complete_imports(text):
            if stmt.kind == "export" and not include_export:
                continue
            for token in stmt.modules:
                producer_name = logical_path(stmt, token, prefix)
                if prefix and not producer_name.startswith(prefix + "."):
                    continue
                producer = infos.get(producer_name)
                if producer is None or producer.logical_name == consumer.logical_name:
                    continue
                edge = (consumer.logical_name, producer.logical_name)
                if edge in seen_edges:
                    continue
                seen_edges.add(edge)
                import_edges += 1

                edge_key = (consumer.vfile[:-2], producer.vfile[:-2])

                symbol_keys = {
                    (ref.secpath, ref.name)
                    for ref in consumer.refs
                    if ref.module == producer.logical_name
                }
                if not symbol_keys:
                    # Dead imports and pure re-export forwarding are the other
                    # checker's job; this report only ranks genuinely live edges.
                    edge_weaknesses[edge_key] = EdgeWeakness(
                        *edge_key, status="no_symbols"
                    )
                    continue
                unmatched = [
                    key for key in symbol_keys
                    if key not in producer.alias_to_unit
                ]
                direct_symbols = tuple(sorted(
                    _display_symbol(*key) for key in symbol_keys
                ))
                unmatched_symbols += len(unmatched)
                # If even one referenced symbol cannot be assigned to a
                # declaration unit, omitting it would understate the closure.
                # Suppress the entire edge instead of reporting a potentially
                # false weak dependency from only the roots we understood.
                if unmatched:
                    edge_weaknesses[edge_key] = EdgeWeakness(
                        *edge_key,
                        status="unmapped",
                        unmatched_symbols=len(unmatched),
                        direct_symbols=direct_symbols,
                    )
                    continue
                roots = {
                    producer.alias_to_unit[key]
                    for key in symbol_keys
                }
                if not roots:
                    continue
                live_symbol_edges += 1
                closure = _closure(producer, roots)
                total = len(producer.units)
                if total == 0:
                    continue
                measurement = {
                    "direct_count": len(roots),
                    "closure_count": len(closure),
                    "producer_units": total,
                    "direct_symbols": direct_symbols,
                }
                if len(closure) / total > max_fraction:
                    edge_weaknesses[edge_key] = EdgeWeakness(
                        *edge_key, status="not_weak", **measurement
                    )
                    continue

                # This edge is symbolically weak, but it only matters to build
                # serialization if it adds a new prerequisite.  If A is already
                # reachable from another direct import C (C ->* A), B's explicit
                # B -> A edge does not lengthen or constrain the Require DAG.
                other_imports = import_graph.get(consumer.logical_name, set()) - {
                    producer.logical_name
                }
                if any(
                    producer.logical_name in transitive_imports(
                        import_graph, other, import_closure_cache
                    )
                    for other in other_imports
                ):
                    transitively_covered_edges += 1
                    edge_weaknesses[edge_key] = EdgeWeakness(
                        *edge_key, status="covered", **measurement
                    )
                    continue
                if is_expected_producer(producer.vfile):
                    expected_producer_edges += 1
                    edge_weaknesses[edge_key] = EdgeWeakness(
                        *edge_key, status="expected", **measurement
                    )
                    continue

                edge_weaknesses[edge_key] = EdgeWeakness(
                    *edge_key, status="weak", **measurement
                )

                direct_units = sorted(producer.units[i].label for i in roots)
                closure_units = sorted(producer.units[i].label for i in closure)
                referenced_modules: set[str] = set()
                for index in closure:
                    referenced_modules |= producer.units[index].referenced_modules
                local_prerequisites = sorted(
                    module[len(prefix) + 1:]
                    for module in referenced_modules
                    if prefix and module.startswith(prefix + ".")
                    and module != producer.logical_name
                )
                candidates.append(
                    Candidate(
                        consumer=consumer.vfile,
                        producer=producer.vfile,
                        import_line=stmt.lineno,
                        import_kind=stmt.kind,
                        producer_lines=producer.lines,
                        producer_units=total,
                        direct_units=direct_units,
                        direct_symbols=list(direct_symbols),
                        closure_units=closure_units,
                        local_prerequisites=local_prerequisites,
                    )
                )

    # The fraction is intentionally the sole ranking metric as well as the sole
    # eligibility metric.  File/location fields only make equal fractions
    # deterministic.
    candidates.sort(
        key=lambda item: (
            item.fraction,
            item.consumer,
            item.import_line,
            item.producer,
        )
    )
    return Analysis(
        candidates=candidates,
        project_files=len(all_vfiles),
        usable_files=len(infos),
        import_edges=import_edges,
        live_symbol_edges=live_symbol_edges,
        skipped_files=skipped,
        unmatched_symbols=unmatched_symbols,
        transitively_covered_edges=transitively_covered_edges,
        expected_producer_edges=expected_producer_edges,
        edge_weaknesses=edge_weaknesses,
    )


def _short_list(items: list[str], limit: int = 5) -> str:
    shown = items[:limit]
    value = ", ".join(f"`{item}`" for item in shown)
    if len(items) > limit:
        value += f", +{len(items) - limit} more"
    return value or "_(none)_"


def render_markdown(
    result: Analysis,
    *,
    top: int,
    max_fraction: float,
    include_export: bool,
) -> str:
    shown = result.candidates if top == 0 else result.candidates[:top]
    lines = [
        "# Weak import dependency candidates",
        "",
        f"- Analysed **{result.usable_files}** of **{result.project_files}** "
        f"project files and **{result.import_edges}** direct local import edges.",
        f"- **{result.live_symbol_edges}** edges explicitly reference a declaration "
        f"from the imported file; **{len(result.candidates)}** meet the weak-import "
        f"threshold. Showing **{len(shown)}**.",
        f"- Candidate threshold: the explicit transitive closure is at most "
        f"**{max_fraction:.1%}** of the imported file's declaration units. "
        f"This is the only eligibility metric.",
        f"- **{result.transitively_covered_edges}** otherwise-weak edge(s) were "
        f"excluded because the imported file is already in the transitive "
        f"closure of another direct import from the consumer, so the edge adds "
        f"no build serialization.",
        f"- **{result.expected_producer_edges}** serialization-relevant weak "
        f"edge(s) on `KernelDecode*.v` were excluded as expected decode-layer "
        f"dependencies.",
    ]
    if not include_export:
        lines.append("- `Require Export` edges are excluded (use `--include-export` "
                     "to include API/re-export edges).")
    if result.skipped_files:
        lines.append(
            f"- **{len(result.skipped_files)}** files were skipped because their "
            f"`.glob` was missing/stale/unreadable; rebuild before treating this "
            f"as a complete report."
        )
    if result.unmatched_symbols:
        lines.append(
            f"- **{result.unmatched_symbols}** referenced symbol(s) could not be "
            f"mapped to a movable declaration unit; every import edge containing "
            f"one was conservatively suppressed."
        )
    lines += [
        "",
        "This is a refactoring shortlist, not a proof that the dependency can be "
        "rewritten. The closure is a lower bound: tactic, hint, notation-side-effect, "
        "and inference dependencies may be absent from `.glob`.",
        "",
    ]
    if not shown:
        lines.append("_(no import edges meet this threshold)_")
        return "\n".join(lines)

    lines += [
        "| Import edge | Direct | Closure / producer | Producer size |",
        "|---|---:|---:|---:|",
    ]
    for item in shown:
        edge = f"`{item.consumer}:{item.import_line}` → `{item.producer}`"
        lines.append(
            f"| {edge} | {item.direct_count} | {item.closure_count} / "
            f"{item.producer_units} ({item.fraction:.1%}) | "
            f"{item.producer_lines} lines |"
        )

    lines += ["", "## Candidate details", ""]
    for number, item in enumerate(shown, start=1):
        lines += [
            f"### {number}. `{item.consumer}:{item.import_line}` → "
            f"`{item.producer}`",
            "",
            f"- Directly referenced symbols ({len(item.direct_symbols)}): "
            f"{_short_list(item.direct_symbols, 12)}.",
            f"- Direct declaration units ({item.direct_count}): "
            f"{_short_list(item.direct_units, 12)}.",
            f"- Explicit internal closure ({item.closure_count} of "
            f"{item.producer_units}): {_short_list(item.closure_units, 12)}.",
            f"- Other local modules referenced by that closure: "
            f"{_short_list(item.local_prerequisites, 12)}.",
            "",
        ]
    if top and len(result.candidates) > len(shown):
        lines.append(
            f"_Omitted {len(result.candidates) - len(shown)} additional candidates; "
            f"rerun with `--top 0` to show all._"
        )
    return "\n".join(lines)


def main() -> int:
    parser = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter
    )
    parser.add_argument("--dir", default=".",
                        help="directory containing _CoqProject, .v, and .glob files")
    parser.add_argument("--files", nargs="*", default=None,
                        help="restrict importing/consumer files (default: all)")
    parser.add_argument("--max-fraction", type=float, default=0.10,
                        help="maximum closure/producer ratio, 0..1 (default: .10)")
    parser.add_argument("--include-export", action="store_true",
                        help="also analyse Require Export edges")
    parser.add_argument("--allow-stale", action="store_true",
                        help="use stale .glob files (may miss references from edits)")
    parser.add_argument("--top", type=int, default=50,
                        help="show this many ranked candidates; 0 means all (default: 50)")
    parser.add_argument("--format", choices=("md", "json"), default="md")
    parser.add_argument("--report", default=None,
                        help="also write the report to this path")
    args = parser.parse_args()

    if not 0 < args.max_fraction <= 1:
        parser.error("--max-fraction must be > 0 and <= 1")
    if args.top < 0:
        parser.error("--top must be >= 0")

    result = analyze(
        args.dir,
        files=args.files,
        max_fraction=args.max_fraction,
        include_export=args.include_export,
        allow_stale=args.allow_stale,
    )
    if args.format == "json":
        shown = result.candidates if args.top == 0 else result.candidates[:args.top]
        output = json.dumps(
            {
                "summary": {
                    "project_files": result.project_files,
                    "usable_files": result.usable_files,
                    "import_edges": result.import_edges,
                    "live_symbol_edges": result.live_symbol_edges,
                    "candidate_edges": len(result.candidates),
                    "shown": len(shown),
                    "skipped_files": result.skipped_files,
                    "unmatched_symbols": result.unmatched_symbols,
                    "transitively_covered_edges":
                        result.transitively_covered_edges,
                    "expected_producer_edges": result.expected_producer_edges,
                },
                "thresholds": {
                    "max_fraction": args.max_fraction,
                    "include_export": args.include_export,
                },
                "candidates": [candidate.as_dict() for candidate in shown],
            },
            indent=2,
            sort_keys=True,
        )
    else:
        output = render_markdown(
            result,
            top=args.top,
            max_fraction=args.max_fraction,
            include_export=args.include_export,
        )
    print(output)
    if args.report:
        with open(args.report, "w") as report:
            report.write(output + "\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
