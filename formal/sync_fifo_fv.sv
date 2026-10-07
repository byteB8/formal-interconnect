// Formal testbench for sync_fifo.
//
// Every input is free: the solver may push, pop and pick data in any pattern,
// on any cycle. No assumptions are needed, because the FIFO ignores illegal
// operations itself. The runner forces a reset in the first cycle
// (ebmc --reset sync_fifo_fv.rst==1); after that rst is free too, so the
// properties also cover a reset arriving in the middle of traffic.

`ifndef FIFO_WIDTH
`define FIFO_WIDTH 8
`endif
`ifndef FIFO_DEPTH
`define FIFO_DEPTH 4
`endif

module sync_fifo_fv #(
  parameter int WIDTH = `FIFO_WIDTH,
  parameter int DEPTH = `FIFO_DEPTH
) (
  input logic             clk,
  input logic             rst,
  input logic             push,
  input logic [WIDTH-1:0] push_data,
  input logic             pop,
  input logic             track       // free: marks the push the tracker follows
);
  localparam AW = $clog2(DEPTH);
  localparam CW = AW + 1;

  logic             full;
  logic             empty;
  logic [WIDTH-1:0] pop_data;
  logic [CW-1:0]    count;

  sync_fifo #(.WIDTH(WIDTH), .DEPTH(DEPTH)) dut (
    .clk(clk), .rst(rst),
    .push(push), .push_data(push_data), .full(full),
    .pop(pop), .pop_data(pop_data), .empty(empty),
    .count(count)
  );

  default clocking @(posedge clk); endclocking
  default disable iff (rst);

  // Handshakes that take effect, derived from the ports alone.
  logic push_ok;
  logic pop_ok;
  assign push_ok = push && !full;
  assign pop_ok  = pop && !empty;

  // ------------------------------------------------------------------
  // Occupancy and flags
  // ------------------------------------------------------------------
  a_count_range: assert property (count <= DEPTH);
  a_full_flag:   assert property (full == (count == DEPTH));
  a_empty_flag:  assert property (empty == (count == 0));

  // count moves by exactly the handshakes that took effect: an ignored push
  // (while full) or pop (while empty) must not change it.
  a_count_up:    assert property (push_ok && !pop_ok |=> count == $past(count) + 1'b1);
  a_count_down:  assert property (pop_ok && !push_ok |=> count == $past(count) - 1'b1);
  a_count_hold:  assert property (push_ok == pop_ok  |=> $stable(count));

  // Reset empties the FIFO. This one must see reset, so it overrides the
  // default disable.
  a_reset: assert property (disable iff (1'b0) rst |=> empty && count == 0);

  // ------------------------------------------------------------------
  // Data integrity and ordering: follow one symbolic entry
  // ------------------------------------------------------------------
  // Rather than modelling the whole FIFO, the testbench follows one push,
  // chosen by the solver through the free `track` input. It records the
  // pushed value and how many entries were ahead of it, counts that number
  // down as entries leave, and checks that the entry is on pop_data exactly
  // when nothing is left ahead of it. The solver can pick any push and any
  // data, so a proof covers every entry: none is lost, corrupted, overtaken
  // or delivered early.
  logic             tracking;
  logic [WIDTH-1:0] tracked;
  logic [CW-1:0]    ahead;

  always_ff @(posedge clk) begin
    if (rst) begin
      tracking <= 1'b0;
    end else if (!tracking) begin
      if (push_ok && track) begin
        tracking <= 1'b1;
        tracked  <= push_data;
        ahead    <= count - pop_ok;    // an entry popped this cycle is no longer ahead
      end
    end else if (pop_ok) begin
      if (ahead == 0) tracking <= 1'b0;   // the tracked entry itself left
      else            ahead    <= ahead - 1'b1;
    end
  end

  a_track_inside: assert property (tracking |-> ahead < count);
  a_data_order:   assert property (tracking && ahead == 0 |-> pop_data == tracked);

  // ------------------------------------------------------------------
  // Helper lemma for the unbounded proof
  // ------------------------------------------------------------------
  // a_data_order is true but not inductive: k-induction may start from an
  // unreachable state where the tracked value is not in memory at all, and
  // refute it from there. The lemma rules those states out by saying where
  // the tracked value lives: `ahead` slots after the read pointer.
  //
  // EBMC proves each assertion in isolation, so a lemma only helps once it
  // is an assumption. The runner therefore proves h_tracker_inv first, on its
  // own, and then proves the a_ properties with -D USE_LEMMAS, which turns
  // the (already proven) lemma into an assumption. For the first step to
  // work the lemma must be inductive by itself, which is why it also carries
  // the occupancy bounds it depends on. It reads DUT internals, so it is the
  // one white-box property in this file.
  property p_tracker_inv;
    count <= DEPTH &&
    (!tracking || (ahead < count &&
                   dut.mem[dut.rd_ptr[AW-1:0] + ahead[AW-1:0]] == tracked));
  endproperty

`ifdef USE_LEMMAS
  h_tracker_inv: assume property (p_tracker_inv);
`else
  h_tracker_inv: assert property (p_tracker_inv);
`endif

  // ------------------------------------------------------------------
  // Covers: each must be reachable, or a property above could pass
  // vacuously.
  // ------------------------------------------------------------------
  c_full:          cover property (full);
  c_full_to_empty: cover property (full ##[1:$] empty);
  c_push_pop_full: cover property (full && push && pop);       // push dropped, pop taken
  // This pop wraps the read pointer. Not written as $fell(dut.rd_ptr[AW]):
  // that is also satisfied by reset clearing a pointer that started high, so
  // it would report coverage with no traffic at all.
  c_rd_wrap:       cover property (pop_ok && dut.rd_ptr == '1);
  c_track_deep:    cover property (tracking && ahead == DEPTH - 1);
  c_track_out:     cover property (tracking && ahead == 0 && pop_ok);
endmodule
