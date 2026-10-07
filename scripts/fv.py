#!/usr/bin/env python3
"""Run the formal checks for each block and report what was proved.

    scripts/fv.py prove [BLOCK ...]   unbounded proofs, bounded checks and covers
    scripts/fv.py bugs  [BLOCK ...]   seed each bug in bugs/bugs.toml, check it is caught
    scripts/fv.py study               FIFO proof with and without its helper lemma
    scripts/fv.py all                 prove + bugs + study, then write results/

Property names carry their role in a prefix: a_ is a specification
assertion, h_ a helper lemma, c_ a cover and m_ an environment assumption.

Needs EBMC 6.0 (`ebmc`) and Spot's `ltl2tgba` on PATH; `make` adds the
default install locations.
"""

import argparse
import json
import shutil
import subprocess
import sys
import tempfile
import time
import tomllib
from dataclasses import dataclass
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
RESULTS = ROOT / "results"


@dataclass(frozen=True)
class Block:
    name: str
    k: int                          # induction depth for the unbounded proof
    cover_depth: int                # BMC depth for covers and bounded-only checks
    bug_depth: int                  # BMC depth when hunting seeded bugs
    lemmas: bool = False            # has h_ lemmas: prove them first, then assume them
    bounded_only: tuple = ()        # properties k-induction cannot take; BMC only

    @property
    def top(self):
        return f"{self.name}_fv"

    def sources(self, rtl_dir):
        return [rtl_dir / f"{self.name}.sv", ROOT / "formal" / f"{self.top}.sv"]


BLOCKS = {b.name: b for b in [
    Block("sync_fifo", k=1, cover_depth=14, bug_depth=12, lemmas=True),
    Block("rr_arbiter", k=3, cover_depth=12, bug_depth=12, bounded_only=("a_eventually",)),
    Block("skid_buffer", k=1, cover_depth=12, bug_depth=12, lemmas=True),
]}


def role(name):
    return {"a": "assert", "h": "lemma", "c": "cover", "m": "assume"}.get(name[0], "other")


def ebmc(block, *args, rtl_dir=None, defines=(), timeout=900, allow_timeout=False, vcd=None):
    """Run EBMC on one block.

    Returns ({property: (status, trace_length)}, seconds). trace_length is the
    number of cycles in the counterexample or cover witness, if there is one.
    A timeout is fatal unless allow_timeout is set, in which case the result
    is (None, timeout).
    """
    with tempfile.TemporaryDirectory() as tmp:
        result = Path(tmp) / "result.json"
        cmd = ["ebmc", *map(str, block.sources(rtl_dir or ROOT / "rtl")),
               "--top", block.top, "--reset", f"{block.top}.rst==1", "--buechi",
               "--json-result", str(result), *map(str, args)]
        for d in defines:
            cmd += ["-D", d]
        if vcd:
            cmd += ["--vcd", str(Path(tmp) / "cex")]
        start = time.monotonic()
        try:
            proc = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout)
        except subprocess.TimeoutExpired:
            if not allow_timeout:
                sys.exit(f"ebmc timed out after {timeout} s:\n  {' '.join(cmd)}")
            return None, timeout
        seconds = time.monotonic() - start
        if not result.exists():
            sys.exit(f"ebmc failed:\n  {' '.join(cmd)}\n{proc.stdout[-3000:]}{proc.stderr[-3000:]}")
        data = json.loads(result.read_text())
        if vcd:
            for f in Path(tmp).glob("cex*.vcd"):
                Path(vcd).parent.mkdir(parents=True, exist_ok=True)
                shutil.move(f, vcd)
    props = {}
    for p in data["properties"]:
        name = p["identifier"].rsplit(".", 1)[-1]
        trace = p.get("trace")
        props[name] = (p["status"], len(trace["states"]) if trace else None)
    return props, seconds


def deepen(block, max_depth, rtl_dir=None):
    """Bounded model checking at bounds 1..max_depth.

    EBMC's counterexamples and cover witnesses are not minimal, so the
    shortest one is found by deepening the bound. Returns (first, last,
    seconds): first maps each property to the smallest bound, i.e. the cycle
    after reset, at which an assertion or lemma fails or a cover is hit;
    last is the result at max_depth.
    """
    first, seconds, res = {}, 0.0, {}
    for bound in range(1, max_depth + 1):
        res, secs = ebmc(block, "--bound", bound, rtl_dir=rtl_dir)
        seconds += secs
        for name, (status, _) in res.items():
            if role(name) == "cover":
                hit = status == "PROVED"
            else:
                hit = role(name) in ("assert", "lemma") and status == "REFUTED"
            if hit and name not in first:
                first[name] = bound
    return first, res, seconds


# ----------------------------------------------------------------------------
# prove
# ----------------------------------------------------------------------------

def prove(block):
    """Unbounded proofs (k-induction), then bounded checks and covers (BMC)."""
    rows = {}
    timing = {}
    kind_args = ("--k-induction", "--bound", block.k)

    # 1. Helper lemmas, each inductive on its own.
    lemmas_ok = True
    if block.lemmas:
        res, timing["lemmas"] = ebmc(block, *kind_args)
        for name, (status, _) in res.items():
            if role(name) == "lemma":
                ok = status == "PROVED"
                lemmas_ok &= ok
                rows[name] = ("lemma", f"proved ({block.k}-induction)" if ok else f"NOT PROVED: {status}")

    # 2. Assertions, with the proven lemmas assumed.
    defines = ["USE_LEMMAS"] if block.lemmas and lemmas_ok else []
    res, timing["asserts"] = ebmc(block, *kind_args, defines=defines)
    for name, (status, _) in res.items():
        if role(name) == "assert" and name not in block.bounded_only:
            how = f"{block.k}-induction" + (", lemmas assumed" if defines else "")
            rows[name] = ("assert", f"proved ({how})" if status == "PROVED" else f"NOT PROVED: {status}")

    # 3. Covers and the checks only BMC can take, deepening the bound so each
    #    cover reports its shortest witness.
    first, res, timing["bmc"] = deepen(block, block.cover_depth)
    for name, (status, _) in res.items():
        if role(name) == "cover":
            rows[name] = ("cover", f"covered at cycle {first[name]}" if name in first
                          else f"NOT COVERED within {block.cover_depth} cycles")
        elif name in block.bounded_only:
            rows[name] = ("assert", f"FAILED at cycle {first[name]}" if name in first
                          else f"bounded: holds to cycle {block.cover_depth}")
        elif name in first:
            # A proved property must never fail in BMC; if it does, a lemma
            # assumption was unsound and the proof above cannot be trusted.
            rows[name] = (role(name), f"INCONSISTENT: proved, yet fails at cycle {first[name]}")
    return rows, timing


def proof_complete(rows):
    return all(v.startswith(("proved", "covered", "bounded")) for _, v in rows.values())


# ----------------------------------------------------------------------------
# bugs
# ----------------------------------------------------------------------------

def load_bugs():
    return tomllib.loads((ROOT / "bugs" / "bugs.toml").read_text())["bug"]


def hunt(bug):
    """Seed one bug into a copy of the RTL and look for counterexamples."""
    block = BLOCKS[bug["block"]]
    rtl = (ROOT / "rtl" / f"{block.name}.sv").read_text()
    if rtl.count(bug["find"]) != 1:
        sys.exit(f"bug {bug['id']}: `find` must occur exactly once in rtl/{block.name}.sv")
    with tempfile.TemporaryDirectory() as tmp:
        (Path(tmp) / f"{block.name}.sv").write_text(rtl.replace(bug["find"], bug["replace"]))
        first, _, seconds = deepen(block, block.bug_depth, rtl_dir=Path(tmp))
        failed = sorted((cycle, name) for name, cycle in first.items()
                        if role(name) in ("assert", "lemma"))
        if failed:
            # Keep a waveform of the shortest counterexample for GTKWave/Surfer.
            cycle, name = failed[0]
            ebmc(block, "--bound", cycle, "--property", f"{block.top}.{name}",
                 rtl_dir=Path(tmp), vcd=RESULTS / "cex" / f"{bug['id']}.vcd")
    caught_by_spec = any(role(n) == "assert" for _, n in failed)
    return {"id": bug["id"], "block": block.name, "what": bug["what"],
            "caught": caught_by_spec, "failed": [(n, c) for c, n in failed],
            "seconds": round(seconds, 2)}


# ----------------------------------------------------------------------------
# study: what the FIFO helper lemma buys
# ----------------------------------------------------------------------------

def study(depths=(4, 16, 64, 256), ks=(1, 2, 4, 8, 16), timeout=300):
    block = BLOCKS["sync_fifo"]
    out = []
    for depth in depths:
        defs = [f"FIFO_DEPTH={depth}"]
        # With the lemma: prove it, then every assertion assuming it.
        lem, t_lem = ebmc(block, "--k-induction", "--bound", 1, "--property",
                          f"{block.top}.h_tracker_inv", defines=defs,
                          timeout=timeout, allow_timeout=True)
        res, t_all = ebmc(block, "--k-induction", "--bound", 1, defines=defs + ["USE_LEMMAS"],
                          timeout=timeout, allow_timeout=True)
        with_lemma = (lem and lem["h_tracker_inv"][0] == "PROVED" and res and
                      all(s == "PROVED" for n, (s, _) in res.items() if role(n) == "assert"))
        row = {"depth": depth, "storage_bits": depth * 8,
               "with_lemma": "proved" if with_lemma else "not proved",
               "with_lemma_seconds": round(t_lem + t_all, 2), "without_lemma": {}}
        # Without it: a_data_order alone, for growing k.
        for k in ks:
            res, secs = ebmc(block, "--k-induction", "--bound", k, "--property",
                             f"{block.top}.a_data_order", defines=defs,
                             timeout=timeout, allow_timeout=True)
            status = "timeout" if res is None else res["a_data_order"][0].lower()
            row["without_lemma"][k] = (status, round(secs, 2))
            if res is None:
                break
        out.append(row)
    return out


# ----------------------------------------------------------------------------
# reporting
# ----------------------------------------------------------------------------

def print_prove(name, rows, timing):
    print(f"\n{name}  ({', '.join(f'{k} {v:.2f}s' for k, v in timing.items())})")
    for prop, (r, verdict) in rows.items():
        print(f"  {r:7} {prop:18} {verdict}")


def print_bug(b):
    mark = "caught" if b["caught"] else "MISSED"
    fails = ", ".join(f"{n}@{c}" for n, c in b["failed"])
    print(f"  {mark:6} {b['id']:28} {fails}")


def write_results(proofs, bugs, study_rows):
    RESULTS.mkdir(exist_ok=True)
    (RESULTS / "summary.json").write_text(json.dumps(
        {"proofs": proofs, "bugs": bugs, "study": study_rows}, indent=2) + "\n")

    lines = ["# Results", "",
             "Generated by `scripts/fv.py all` with EBMC 6.0. Do not edit by hand.", ""]
    lines += ["## Proofs", ""]
    for name, p in proofs.items():
        timing = ", ".join(f"{k} {v:.2f} s" for k, v in p["timing"].items())
        lines += [f"### {name}", "", f"Run time: {timing}.", "",
                  "| Property | Role | Result |", "|---|---|---|"]
        lines += [f"| `{prop}` | {r} | {v} |" for prop, (r, v) in p["rows"].items()]
        lines.append("")
    caught = sum(b["caught"] for b in bugs)
    lines += ["## Seeded bugs", "", f"{caught} of {len(bugs)} caught by a specification "
              "assertion (`a_`). Each failing property is listed with the earliest cycle "
              "after reset at which it fails. The shortest counterexample of each bug is "
              "saved as a waveform in `results/cex/`.", "",
              "| Bug | Block | What changed | Caught | Failing properties (cycle) |",
              "|---|---|---|---|---|"]
    for b in bugs:
        fails = ", ".join(f"`{n}` ({c})" for n, c in b["failed"]) or "none"
        lines.append(f"| `{b['id']}` | {b['block']} | {b['what']} | "
                     f"{'yes' if b['caught'] else '**no**'} | {fails} |")
    if study_rows:
        ks = list(study_rows[0]["without_lemma"])
        lines += ["", "## FIFO: what the helper lemma buys", "",
                  "WIDTH 8. *With lemma*: prove `h_tracker_inv` by 1-induction, then all nine "
                  "FIFO assertions assuming it; the time covers both runs. *Without*: "
                  "`a_data_order` alone by k-induction, for growing k.", "",
                  "| Depth | Storage bits | With lemma | Without, "
                  + " | ".join(f"k={k}" for k in ks) + " |",
                  "|---|---|---|" + "---|" * len(ks)]
        for r in study_rows:
            cells = []
            for k in ks:
                status, secs = r["without_lemma"].get(k, ("-", 0))
                cells.append("-" if status == "-" else f"{status} ({secs} s)")
            lines.append(f"| {r['depth']} | {r['storage_bits']} | {r['with_lemma']} "
                         f"({r['with_lemma_seconds']} s) | " + " | ".join(cells) + " |")
    (RESULTS / "summary.md").write_text("\n".join(lines) + "\n")


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("command", choices=["prove", "bugs", "study", "all"])
    ap.add_argument("blocks", nargs="*", help=f"any of {', '.join(BLOCKS)} (default: all)")
    args = ap.parse_args()
    unknown = set(args.blocks) - set(BLOCKS)
    if unknown:
        ap.error(f"unknown block(s): {', '.join(sorted(unknown))}")
    for tool in ("ebmc", "ltl2tgba"):
        if not shutil.which(tool):
            sys.exit(f"{tool} not found on PATH; run through `make`, or see README.md")
    names = args.blocks or list(BLOCKS)

    proofs, bugs, study_rows = {}, [], []
    if args.command in ("prove", "all"):
        for name in names:
            rows, timing = prove(BLOCKS[name])
            proofs[name] = {"rows": rows, "timing": timing}
            print_prove(name, rows, timing)
    if args.command in ("bugs", "all"):
        print("\nseeded bugs")
        for bug in load_bugs():
            if bug["block"] in names:
                bugs.append(hunt(bug))
                print_bug(bugs[-1])
    if args.command in ("study", "all"):
        print("\nFIFO lemma study")
        study_rows = study()
        for r in study_rows:
            print(f"  depth {r['depth']}: with lemma {r['with_lemma']} ({r['with_lemma_seconds']} s);"
                  f" without: {r['without_lemma']}")
    if args.command == "all":
        write_results(proofs, bugs, study_rows)
        print(f"\nwrote {RESULTS / 'summary.md'}")

    ok = all(proof_complete(p["rows"]) for p in proofs.values()) and all(b["caught"] for b in bugs)
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
