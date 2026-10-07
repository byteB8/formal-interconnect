# formal-interconnect

Formal verification of three on-chip interconnect blocks, written in
SystemVerilog and specified with SystemVerilog Assertions (SVA): a synchronous
FIFO, a round-robin arbiter and a valid/ready skid buffer. Everything runs on
open-source tools, using the EBMC model checker with Spot for temporal
properties.

## Results

All figures come from [`results/summary.md`](results/summary.md), which
`make all` regenerates.

| Block | Spec assertions | Unbounded proofs | Covers reached | Seeded bugs caught |
|---|---|---|---|---|
| `sync_fifo` | 9 | 9 (1-induction, 1 lemma) | 6 / 6 | 5 / 5 |
| `rr_arbiter` | 5 | 4 (3-induction) + 1 liveness check to depth 12 | 3 / 3 | 4 / 4 |
| `skid_buffer` | 8 | 8 (1-induction, 1 lemma) | 6 / 6 | 5 / 5 |

- **Data integrity without a reference model.** Each FIFO and skid-buffer
  entry is followed as a single symbolic transaction, so a proof covers every
  entry and every data value. With one helper lemma, the full FIFO proof
  closes at depth 256 (2,048 bits of storage) in 9.4 s. Without the lemma,
  k-induction stays inconclusive at every depth and every k tried.
- **Fairness, proved.** Every request is granted within N−1 cycles, for every
  requester at once (symbolic index). A cover shows the bound is tight.
- **14 of 14 seeded bugs caught.** Each counterexample is reported at its
  earliest failing cycle, and its waveform is saved in `results/cex/`. The
  bugs include a performance bug: a skid buffer that delivers correct data at
  half throughput.
- **Three EBMC 6.0 bugs hit and worked around**, each confirmed against an
  independent result: `$onehot0` returns wrong results (already fixed for
  6.1), an expression used as a `##[m:n]` bound is mis-evaluated, and
  properties in a for-generate loop give spurious counterexamples. See
  [`docs/findings.md`](docs/findings.md).

`make prove` takes about 17 s on a 4-core laptop; `make all` about 2 minutes.

## What is checked

The full requirement-by-requirement plan is in
[`docs/verification_plan.md`](docs/verification_plan.md). In short:

- **`sync_fifo`** (first-word fall-through, parameterised width and depth).
  Occupancy and flags are always consistent. Ignored pushes and pops change
  nothing. Reset empties it. Every entry comes out unchanged, in order,
  exactly once. No environment assumptions: it must work for any input
  sequence.
- **`rr_arbiter`** (masked priority with wrap-around, no loops in the RTL).
  At most one grant, only to a requester, never idle while someone waits.
  Every request is granted within N−1 cycles, provided requests are held
  until granted.
- **`skid_buffer`** (registered outputs, ready driven from state only). The
  downstream sees legal valid/ready behaviour. `s_ready` is high exactly when
  there is room. At most two beats are held. No bubbles are added. Every beat
  comes out unchanged, in order, exactly once.

## Techniques

- **Symbolic transaction tracking.** A free input picks which push to follow.
  The testbench records its value and the number of entries ahead of it, and
  checks it arrives exactly when that number reaches zero. This is a
  data-independence abstraction: the extra state is constant in the depth,
  whereas a full reference model doubles the state to verify.
- **Helper lemmas, proved then assumed.** EBMC's k-induction proves each
  assertion in isolation. Lemmas (`h_`) are therefore proved first, each
  inductive on its own, and then become assumptions (`-D USE_LEMMAS`) for the
  specification proof. As a soundness guard, every proved property is also
  bounded-checked, and any failure is flagged as `INCONSISTENT`.
- **Symbolic index.** The fairness properties watch one requester chosen by
  the solver, rather than N copies of each property.
- **Environment by construction.** The rules the environment must follow
  (requests held until granted; upstream holds valid and data until
  accepted) are built into the stimulus, not stated as assumptions. That
  keeps every proof within what k-induction supports.
- **Covers against vacuity**, each reported at its shortest witness. One
  caught a vacuous check during development: a pointer-wrap cover that was
  satisfied by reset alone.
- **Bounded response versus liveness.** The arbiter's N−1 bound is a safety
  property, proved unbounded, and it implies liveness. The `s_eventually`
  form is kept as a bounded check, where it reports starvation as a
  lasso-shaped counterexample.

## Running it

Requirements: Python 3.11 or newer, EBMC 6.0 and Spot's `ltl2tgba`. None of
them needs root:

```bash
mkdir -p ~/opt && cd ~/opt

# EBMC 6.0: a single static binary inside a .deb; unpack it rather than install it
wget https://github.com/diffblue/hw-cbmc/releases/download/ebmc-6.0/ebmc_6.0_amd64.deb
dpkg-deb -x ebmc_6.0_amd64.deb ~/opt/ebmc

# Spot (provides ltl2tgba), from conda-forge through a standalone micromamba
curl -L -o micromamba https://github.com/mamba-org/micromamba-releases/releases/latest/download/micromamba-linux-64
chmod +x micromamba
MAMBA_ROOT_PREFIX=~/opt/mamba-root ./micromamba create -y -p ~/opt/spot -c conda-forge spot
```

Then, from this directory:

```bash
make prove    # unbounded proofs, bounded checks and covers
make bugs     # seed each bug in bugs/bugs.toml and check it is caught
make study    # FIFO proof with and without its helper lemma
make all      # all three, and regenerate results/
```

The Makefile looks for the tools under `~/opt`; point it elsewhere with
`make EBMC_BIN=... SPOT_BIN=...`. To view a counterexample, open its file
from `results/cex/` in GTKWave or Surfer; both come with the
[OSS CAD Suite](https://github.com/YosysHQ/oss-cad-suite-build).

A single property can be run directly, for example:

```bash
ebmc rtl/rr_arbiter.sv formal/rr_arbiter_fv.sv --top rr_arbiter_fv \
     --reset rr_arbiter_fv.rst==1 --buechi --k-induction --bound 3
```

## Layout

```
rtl/        the three designs
formal/     one formal testbench per design: stimulus, properties, lemmas, covers
bugs/       bugs.toml, the seeded design mistakes
scripts/    fv.py, which runs every check and writes results/
docs/       verification plan and findings
results/    generated: summary.md, summary.json, counterexample waveforms
```

## Tool versions

EBMC 6.0 (June 2026), Spot 2.16, Python 3.12. OSS CAD Suite 2026-10-07 was
used for simulation (Icarus Verilog) and waveform viewing.
