// Round-robin arbiter.
//
// Grants at most one requester per cycle, combinationally from req. Priority
// rotates: after requester i wins, requesters above i are preferred, lowest
// index first, and only when none of them is requesting does the search wrap
// around to index 0. Every waiting requester is therefore served within N-1
// cycles, provided it keeps requesting.
//
// mask_q holds the requesters above the last winner. Masking req with it and
// isolating the lowest set bit picks the winner without a loop; when the
// masked set is empty the arbiter falls back to the whole request vector,
// which is the wrap-around.
module rr_arbiter #(
  parameter int N = 4       // number of requesters, at least 2
) (
  input  logic         clk,
  input  logic         rst,     // synchronous, active high
  input  logic [N-1:0] req,
  output logic [N-1:0] gnt
);
  logic [N-1:0] mask_q;
  logic [N-1:0] masked;
  logic [N-1:0] candidates;

  assign masked     = req & mask_q;
  assign candidates = (masked != '0) ? masked : req;
  assign gnt        = candidates & (~candidates + 1'b1);   // lowest set bit

  always_ff @(posedge clk)
    if (rst)            mask_q <= '1;                       // start from requester 0
    else if (gnt != '0) mask_q <= ~((gnt << 1) - 1'b1);     // everything above the winner
endmodule
