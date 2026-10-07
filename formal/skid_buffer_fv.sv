// Formal testbench for skid_buffer.
//
// The runner forces a reset in the first cycle
// (ebmc --reset skid_buffer_fv.rst==1); after that rst is free.

`ifndef SKID_WIDTH
`define SKID_WIDTH 8
`endif

module skid_buffer_fv #(
  parameter int WIDTH = `SKID_WIDTH
) (
  input logic             clk,
  input logic             rst,
  input logic             src_valid,   // free: whether the source offers a new beat
  input logic [WIDTH-1:0] src_data,    // free: the value of that beat
  input logic             m_ready,     // free: the downstream may stall on any cycle
  input logic             track        // free: marks the beat the tracker follows
);
  logic             s_valid;
  logic             s_ready;
  logic [WIDTH-1:0] s_data;
  logic             m_valid;
  logic [WIDTH-1:0] m_data;

  // ------------------------------------------------------------------
  // Upstream source that obeys the valid/ready rules by construction
  // ------------------------------------------------------------------
  // Once it raises valid it keeps valid and data steady until the beat is
  // accepted; otherwise it may offer anything. This is built into the
  // stimulus rather than written as the usual SVA assumption
  // (s_valid && !s_ready |=> s_valid && $stable(s_data)), which EBMC 6.0's
  // k-induction does not support.
  logic             held_q;
  logic [WIDTH-1:0] held_data_q;

  assign s_valid = held_q || src_valid;
  assign s_data  = held_q ? held_data_q : src_data;

  always_ff @(posedge clk) begin
    if (rst) held_q <= 1'b0;
    else     held_q <= s_valid && !s_ready;
    held_data_q <= s_data;
  end

  skid_buffer #(.WIDTH(WIDTH)) dut (
    .clk(clk), .rst(rst),
    .s_valid(s_valid), .s_ready(s_ready), .s_data(s_data),
    .m_valid(m_valid), .m_ready(m_ready), .m_data(m_data)
  );

  default clocking @(posedge clk); endclocking
  default disable iff (rst);

  logic s_fire;
  logic m_fire;
  assign s_fire = s_valid && s_ready;
  assign m_fire = m_valid && m_ready;

  // ------------------------------------------------------------------
  // Downstream protocol and reset
  // ------------------------------------------------------------------
  // A stalled beat stays offered, unchanged, until it is taken.
  a_down_hold: assert property (m_valid && !m_ready |=> m_valid && $stable(m_data));

  // Reset clears the buffer. Overrides the default disable so it sees reset.
  a_reset: assert property (disable iff (1'b0) rst |=> !m_valid && s_ready);

  // ------------------------------------------------------------------
  // Occupancy, counted from the ports
  // ------------------------------------------------------------------
  // Beats accepted minus beats delivered. Three bits, so a buggy design that
  // overfills shows up as a value above 2 rather than wrapping.
  logic [2:0] occ;

  always_ff @(posedge clk)
    if (rst) occ <= '0;
    else     occ <= occ + s_fire - m_fire;

  a_occ_max:   assert property (occ <= 2);
  a_ready:     assert property (s_ready == (occ < 2));    // ready exactly when there is room
  a_valid:     assert property (m_valid == (occ != 0));   // valid exactly when holding a beat

  // Throughput: one cycle after the downstream is ready, the upstream is
  // ready too, so the buffer never adds bubbles of its own.
  a_no_bubble: assert property (m_ready |=> s_ready);

  // ------------------------------------------------------------------
  // Data integrity and ordering: follow one symbolic beat
  // ------------------------------------------------------------------
  // Same technique as the FIFO testbench: the solver picks any accepted beat
  // through `track`; the testbench counts the beats ahead of it and checks
  // that it is on the output, unchanged, once none are left.
  logic             tracking;
  logic [WIDTH-1:0] tracked;
  logic [2:0]       ahead;

  always_ff @(posedge clk) begin
    if (rst) begin
      tracking <= 1'b0;
    end else if (!tracking) begin
      if (s_fire && track) begin
        tracking <= 1'b1;
        tracked  <= s_data;
        ahead    <= occ - m_fire;     // a beat delivered this cycle is no longer ahead
      end
    end else if (m_fire) begin
      if (ahead == 0) tracking <= 1'b0;   // the tracked beat itself was delivered
      else            ahead    <= ahead - 1'b1;
    end
  end

  a_track_inside: assert property (tracking |-> ahead < occ);
  a_data_order:   assert property (tracking && ahead == 0 |-> m_valid && m_data == tracked);

  // ------------------------------------------------------------------
  // Helper lemma for the unbounded proof
  // ------------------------------------------------------------------
  // Ties the port-level count to the DUT's two registers and says where the
  // tracked beat sits: in the output register when nothing is ahead of it,
  // in the skid register otherwise. Proved on its own first, then assumed
  // (-D USE_LEMMAS) while the a_ properties are proved; see sync_fifo_fv.sv
  // for why EBMC needs the two steps.
  property p_skid_inv;
    occ == dut.m_valid + dut.skid_valid &&
    (!dut.skid_valid || dut.m_valid) &&
    (!tracking || (ahead < occ &&
                   (ahead == 0 ? dut.m_data == tracked : dut.skid_data == tracked)));
  endproperty

`ifdef USE_LEMMAS
  h_skid_inv: assume property (p_skid_inv);
`else
  h_skid_inv: assert property (p_skid_inv);
`endif

  // ------------------------------------------------------------------
  // Covers
  // ------------------------------------------------------------------
  c_skid_used:  cover property (m_valid && !m_ready && s_fire);   // a beat lands in the skid register
  c_full:       cover property (occ == 2);
  c_stream:     cover property ((s_fire && m_fire) [*4]);         // four beats at full rate
  c_src_waits:  cover property (held_q);                          // the source had to wait
  c_track_skid: cover property (tracking && ahead == 1);
  c_track_out:  cover property (tracking && ahead == 0 && m_fire);
endmodule
