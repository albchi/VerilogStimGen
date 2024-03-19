`timescale 10ns/1ns

module gen;

reg clk;
reg rst;

typedef enum {RST, INIT, ADD, SUB, MULT, DIV, REM, HLT} CMD_TYPE ;
reg vld [15:0] = '{0,0,1,0,0,0,0,0,0,0, 0, 0, 0, 0, 0, 0};
reg rdy [15:0] = '{0,0,1,0,0,0,0,0,0,0, 0, 0, 0, 0, 0, 0};
CMD_TYPE cmd [15:0] = '{ADD,SUB,INIT,MULT,DIV,INIT,ADD,REM,INIT,HLT,DIV,RST,SUB,RST,ADD,REM};
reg [63:0] opd1 [15:0] = '{0,0,1,0,0,1,0,1,0,0, 0, 0, 0, 0, 0, 0};
reg [63:0] opd2 [15:0] = '{0,0,1,0,1,0,0,0,0,0, 0, 0, 0, 0, 0, 0};
reg done [15:0] = '{0,0,1,0,1,1,1,0,0,0, 0, 0, 1, 1, 0, 0};
CMD_TYPE done_cmd [15:0] = '{RST, INIT, HLT, ADD,SUB,INIT,MULT,DIV,INIT,ADD,REM,INIT,HLT,DIV,RST,SUB};
reg [3:0] idx;

reg rdy_o;
reg [2:0] cmd_o;
reg [63:0] opd1_o;
reg [63:0] opd2_o;
reg done_i;
reg [2:0] done_cmd_i;


initial begin
   $fsdbDumpvars;
   idx = 0;
   clk = 0;
   rst = 1;
   #500 rst = 0;
   #2500 $finish;
end

always
   #50 clk = ~clk;
   
always @(posedge clk)  begin
   if (rst == 1)  begin
      rdy_o <= 0;
      cmd_o <= 0;
      opd1_o <= 0;
      opd2_o <= 0;
      done_i <= 0;
      done_cmd_i <= 0;
   end
   else begin 
      rdy_o <= rdy[idx];
      cmd_o <= cmd[idx];
      opd1_o <= opd1[idx];
      opd2_o <= opd2[idx];
      done_i <= done[idx];
      done_cmd_i <= done_cmd[idx];
      idx <= idx + 1; 
   end
end




endmodule
