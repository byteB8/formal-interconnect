// Formal testbench for rr_arbiter.
//
// The runner forces a reset in the first cycle (ebmc --reset rr_arbiter_fv.rst==1);
// after that rst is free.

`ifndef ARB_N
`define ARB_N 4
`endif

module rr_arbiter_fv #(
  parameter int N = `ARB_N
) (
  input logic                 clk,
  input logic                 rst,
  input logic [N-1:0]         req_in,   // free: a new request may start on any cycle
  input logic [$clog2(N)-1:0] idx_in    // free: the requester the fairness checks watch
);
  localparam IW = $clog2(N);

  // Longest wait the arbiter promises. Delay and repetition bounds below use
  // this localparam rather than the expression N-1: EBMC 6.0 mis-evaluates an
  // expression written directly as a ##[m:n] bound (see docs/findings.md).
  localparam MAX_WAIT = N - 1;

  // ------------------------------------------------------------------
  // Environment: a request is held until it is granted
  // ------------------------------------------------------------------
  // Without this rule a requester could withdraw just before its turn, and
  // no arbiter could promise it anything. The rule is built into the
  // stimulus rather than written as an SVA assumption: the arbiter sees any
  // new request plus every request it left ungranted last cycle. That is
  // exactly the set of request patterns the rule allows, and it keeps the
  // checks below free of temporal assumptions, which EBMC 6.0's k-induction
  // does not support.
  logic [N-1:0] pending_q;
  logic [N-1:0] req;
  logic [N-1:0] gnt;

  assign req = req_in | pending_q;

  always_ff @(posedge clk)
    if (rst) pending_q <= '0;
    else     pending_q <= req & ~gnt;

  rr_arbiter #(.N(N)) dut (.clk(clk), .rst(rst), .req(req), .gnt(gnt));

  default clocking @(posedge clk); endclocking
  default disable iff (rst);

  // ------------------------------------------------------------------
  // Safety: who may be granted
  // ------------------------------------------------------------------
  // At most one grant. Written out instead of $onehot0(gnt) because EBMC 6.0
  // evaluates $onehot0 wrongly (it accepts 4'b0111), which would let a
  // double grant pass; see docs/findings.md.
  a_one_grant: assert property ((gnt & (gnt - 1'b1)) == '0);
  a_only_req:  assert property ((gnt & ~req) == '0);          // grants go only to requesters
  a_work_cons: assert property (req != '0 |-> gnt != '0);     // never idle while someone waits

  // ------------------------------------------------------------------
  // Fairness, for one requester chosen by the solver
  // ------------------------------------------------------------------
  // idx is picked freely during reset and then held, so the solver may watch
  // any requester and a proof covers all N at once: a symbolic index instead
  // of N copies of each property. (The N copies, written in a for-generate
  // loop, also trip an EBMC 6.0 bug that reports a spurious counterexample;
  // see docs/findings.md.)
  logic [IW-1:0] idx;

  always_ff @(posedge clk)
    if (rst) idx <= idx_in;

  m_idx_valid: assume property (idx < N);   // only binds when N is not a power of two

  // Bounded response: granted within N-1 cycles (0 if it wins at once).
  a_wait_bound: assert property (req[idx] |-> ##[0:MAX_WAIT] gnt[idx]);

  // Liveness: granted eventually. Implied by the bound; kept to exercise the
  // liveness engine and to give lasso-shaped counterexamples for starvation
  // bugs.
  a_eventually: assert property (req[idx] |-> s_eventually gnt[idx]);

  // ------------------------------------------------------------------
  // Covers
  // ------------------------------------------------------------------
  c_wait_max: cover property ((req[idx] && !gnt[idx]) [*MAX_WAIT] ##1 gnt[idx]);  // the bound is tight
  c_all_req:  cover property (req == '1);
  c_wrap:     cover property (gnt[N-1] ##1 gnt[0]);   // priority wraps from the top requester to 0
endmodule
