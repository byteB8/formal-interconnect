// Skid buffer for a valid/ready (AXI-Stream style) channel.
//
// Registers the downstream outputs and drives the upstream ready from state
// only, so no combinational path runs from m_ready back to s_ready, and it
// still moves one beat per cycle while the downstream keeps up. When the
// downstream stalls, a beat that arrives in the same cycle has nowhere to go
// but a second register, the skid register; s_ready drops until that beat
// has moved on.
module skid_buffer #(
  parameter int WIDTH = 8
) (
  input  logic             clk,
  input  logic             rst,        // synchronous, active high

  input  logic             s_valid,
  output logic             s_ready,
  input  logic [WIDTH-1:0] s_data,

  output logic             m_valid,
  input  logic             m_ready,
  output logic [WIDTH-1:0] m_data
);
  logic             skid_valid;
  logic [WIDTH-1:0] skid_data;
  logic             s_fire;
  logic             m_stall;

  assign s_ready = !skid_valid;
  assign s_fire  = s_valid && s_ready;
  assign m_stall = m_valid && !m_ready;

  always_ff @(posedge clk) begin
    if (rst) begin
      m_valid    <= 1'b0;
      skid_valid <= 1'b0;
    end else if (m_stall) begin
      // Output held: a beat accepted now waits in the skid register.
      if (s_fire) begin
        skid_valid <= 1'b1;
        skid_data  <= s_data;
      end
    end else if (skid_valid) begin
      // Output moves on and the parked beat takes its place. s_ready is low,
      // so no new beat arrives this cycle.
      m_valid    <= 1'b1;
      m_data     <= skid_data;
      skid_valid <= 1'b0;
    end else begin
      // Pass-through: the output register takes the incoming beat, if any.
      m_valid <= s_valid;
      m_data  <= s_data;
    end
  end
endmodule
