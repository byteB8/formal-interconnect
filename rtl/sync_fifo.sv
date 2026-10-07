// Synchronous FIFO with first-word fall-through.
//
// pop_data shows the head entry whenever the FIFO is not empty, so a pop
// consumes the value already on pop_data. A push while full and a pop while
// empty are ignored, which keeps the FIFO safe without any assumptions about
// the logic driving it.
//
// The read and write pointers carry one extra wrap bit. The FIFO is empty
// when the pointers are equal and full when they differ only in that bit, so
// no separate occupancy counter is needed.
module sync_fifo #(
  parameter int WIDTH = 8,
  parameter int DEPTH = 4   // power of two, at least 2
) (
  input  logic                   clk,
  input  logic                   rst,        // synchronous, active high

  input  logic                   push,
  input  logic [WIDTH-1:0]       push_data,
  output logic                   full,

  input  logic                   pop,
  output logic [WIDTH-1:0]       pop_data,
  output logic                   empty,

  output logic [$clog2(DEPTH):0] count
);
  localparam AW = $clog2(DEPTH);   // untyped: EBMC 6.0 cannot size "int" from $clog2

  logic [WIDTH-1:0] mem [DEPTH];
  logic [AW:0]      wr_ptr;
  logic [AW:0]      rd_ptr;
  logic             do_push;
  logic             do_pop;

  assign do_push = push && !full;
  assign do_pop  = pop && !empty;

  always_ff @(posedge clk) begin
    if (rst) begin
      wr_ptr <= '0;
      rd_ptr <= '0;
    end else begin
      if (do_push) wr_ptr <= wr_ptr + 1'b1;
      if (do_pop)  rd_ptr <= rd_ptr + 1'b1;
    end
  end

  always_ff @(posedge clk)
    if (!rst && do_push) mem[wr_ptr[AW-1:0]] <= push_data;

  assign empty    = (wr_ptr == rd_ptr);
  assign full     = (wr_ptr == {~rd_ptr[AW], rd_ptr[AW-1:0]});
  assign count    = wr_ptr - rd_ptr;
  assign pop_data = mem[rd_ptr[AW-1:0]];
endmodule
