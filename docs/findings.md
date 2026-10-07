# Findings

Notes from building this flow on open-source tools: three bugs in EBMC 6.0,
the limitations worked around, and lessons about the method itself. Each tool
bug was reproduced on a minimal design and checked against an independent
result (simulation, or an equivalent formulation the tool gets right) before
being treated as a tool bug rather than a design bug.

## Bugs in EBMC 6.0

### 1. `$onehot0` returns wrong results

```systemverilog
module oh(input logic clk, input logic [3:0] x);
  p: assert property (@(posedge clk) $onehot0(x) == ((x & (x - 4'd1)) == 4'd0));
endmodule
```

This is refuted with `x = 4'b0111`, a value with three bits set, for which
`$onehot0` must be false. `$onehot` is evaluated correctly. The EBMC 6.1
changelog lists "Verilog: fix semantics of $onehot0".

Impact: the obvious arbiter assertion, `assert property ($onehot0(gnt))`,
could pass on a design that grants several requesters at once.
`a_one_grant` is therefore written as `(gnt & (gnt - 1)) == 0`, and the
seeded double-grant bug (`arb_no_lowest_bit`) confirms it fails when it
should.

### 2. An expression written as a `##[m:n]` bound is mis-evaluated

With `parameter int D = 2` and `b` equal to `a` delayed by two cycles:

| Property | Expected | EBMC 6.0 |
|---|---|---|
| `a \|-> ##[0:D] b` | holds | proved |
| `a \|-> ##[0:D+1-1] b` | holds | **refuted** |
| `a \|-> ##[0:L] b` with `localparam L = D + 1 - 1` | holds | proved |

Workaround: every delay and repetition bound goes through a localparam
(`MAX_WAIT` in the arbiter testbench).

### 3. Spurious counterexamples for properties inside a for-generate loop

The arbiter fairness check was first written once per requester:

```systemverilog
for (genvar i = 0; i < N; i++) begin : g_fair
  a_wait_bound: assert property (req[i] |-> ##[0:MAX_WAIT] gnt[i]);
end
```

EBMC refuted it for every requester, with and without `--buechi`. The
counterexamples end on the cycle where the requester is first passed over,
three cycles before its `##[0:3]` window closes. Replaying the same inputs in
Icarus Verilog shows the grant arriving on the next cycle, inside the window.
The same property written once outside the loop, for a fixed index or a
symbolic one, is proved. A minimal generate loop over registered signals did
not reproduce the problem, so the trigger is narrower than "any generate
loop".

Workaround: the fairness properties use a symbolic index, `idx`. It is chosen
freely during reset and then held, so one property covers all requesters.
That is a standard abstraction in its own right.

## Limitations worked around

**k-induction proves each assertion in isolation.** In
`src/ebmc/k_induction.cpp`, the induction step adds `assume` properties as
constraints but never other assertions. A helper invariant asserted next to
the property it supports is therefore ignored. The flow proves lemmas (`h_`)
first, each of which must be inductive on its own, and then proves the
specification with `-D USE_LEMMAS`, which turns the proven lemmas into
assumptions. This is sound because a proven invariant holds in every
reachable state, so assuming it removes only unreachable ones. As a guard,
the runner also bounded-checks every proved property and flags any that
fails as `INCONSISTENT`.

**No temporal assumptions under k-induction.** An assumption such as
`req && !gnt |=> req` is reported "unsupported by k-induction", and so is any
`s_eventually`. Both environments (arbiter requests, skid-buffer upstream)
are therefore built into the stimulus rather than assumed. A request vector
`req_in | pending_q` allows exactly the patterns the rule allows.

**Liveness is checked to a bound only.** k-induction rejects `s_eventually`.
The BDD engine with `--buechi` refuted `a_eventually` on the correct arbiter,
even with mid-run reset excluded. That contradicts bounded checking and the
3-induction proof of the stronger `a_wait_bound`. The 6.1 changelog notes
that 6.0's BDD engine silently ignores temporal assumptions. Liveness is
therefore kept as a bounded check, where it finds starvation bugs as
lasso-shaped counterexamples. The unbounded guarantee comes from
`a_wait_bound`, a safety property that implies it.

**IC3 crashes.** `--ic3` failed an internal assertion ("Latch 6 is not
found") on a 4-bit counter. 6.1 lists a refreshed IC3 engine. Unbounded proofs
here use k-induction.

**Unbounded proofs of temporal SVA need Spot.** `--buechi` hands formulas to
Spot's `ltl2tgba`, which is not bundled with EBMC.

**Parser gaps.** EBMC 6.0 does not accept `.name` implicit port connections,
and rejects `localparam int AW = $clog2(DEPTH)` with "type `integer' has
unknown number of bits". The untyped `localparam AW = $clog2(DEPTH)` works.

**Open-source Yosys cannot read concurrent SVA.** Its built-in Verilog front
end rejects `assert property (@(posedge clk) ...)`. The bundled Slang plugin
accepts concurrent assertions only over boolean and `$past` expressions:
`|->`, `|=>`, `##` and sequences are reported as unsupported SVA features.
Full SVA in a Yosys flow needs the commercial Tabby CAD Suite. That is why
EBMC runs the proofs here.

## Lessons about the method

**A cover caught a vacuous check.** `cover property ($fell(dut.rd_ptr[AW]))`
was meant to show the read pointer wrapping. It was reported covered at cycle
1, far too early to be real. The cover was satisfied by reset clearing a
pointer that started high, with no traffic at all. It now requires an actual
pop at the top pointer value (`pop_ok && dut.rd_ptr == '1`), which first
happens at cycle 9.

**Why k-induction needs the FIFO lemma.** Without `h_tracker_inv`,
`a_data_order` stays inconclusive for every k tried (1 to 24 at depth 4),
and run time grows quickly with k. The induction step may start from an
unreachable state where the tracked value is nowhere in memory. Idle cycles
(no push, no pop) keep that state alive for any number of steps, so no k
rules it out. One lemma saying where the tracked value lives makes the
property 1-inductive. Timings are in
[`results/summary.md`](../results/summary.md).

**Counterexample length is not minimal by default.** EBMC returns the first
trace the solver finds, often padded to the full bound. The runner deepens
the bound one cycle at a time, so every reported failure cycle and cover
witness is the shortest possible.
