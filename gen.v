`timescale 10ns/1ns

`define LATENCY 7

module gen;

reg clk;
reg rst;
reg out_of_order_mode;

typedef enum {RST, INIT, ADD, SUB, MULT, DIV, REM, HLT} CMD_TYPE ;
// reg vld [0:15]  = '{0,0,0,0,1,0,0,0,0,0, 0, 0, 0, 0, 0, 0};
reg vld [0:15]  = '{0,0,0,0,1,0,0,1,1,1, 0, 1, 0, 1, 0, 0};
//reg vld [0:15]  = '{0,0,0,0,0,0,0,0,0,0, 0, 0, 0, 0, 0, 0};
reg rdy [0:15]  = '{0,0,1,0,0,0,0,0,0,0, 0, 0, 0, 0, 0, 0};
CMD_TYPE cmd [0:15] = '{INIT,INIT,HLT,REM,SUB,INIT,INIT,ADD,DIV,INIT,INIT,INIT,INIT,INIT,INIT,INIT};
// reg done [0:15] = '{0,0,0,0,0,0,0,0,0,1, 0, 0, 0, 1, 0, 0};
reg done [0:15] = '{0,0,0,0,0,0,0,0,1,0, 1, 0, 0, 1, 0, 0};
reg [63:0] opd1 [0:15] = '{0,0,1,0,0,1,0,1,0,0, 0, 0, 0, 0, 0, 0};
reg [63:0] opd2 [0:15] = '{0,0,1,0,1,0,0,0,0,0, 0, 0, 0, 0, 0, 0};
// CMD_TYPE done_cmd [0:15] = '{RST, INIT, HLT, ADD,SUB,INIT,MULT,DIV,INIT,ADD,REM,INIT,HLT,DIV,RST,SUB};
CMD_TYPE done_cmd [0:15] = '{INIT,INIT,HLT,REM,SUB,INIT,INIT,ADD,DIV,INIT,INIT,INIT,INIT,SUB,INIT,INIT};
reg [3:0] idx;

reg vld_o;
reg rdy_o;
reg [2:0] cmd_o;
reg [63:0] opd1_o;
reg [63:0] opd2_o;
reg done_i;
reg [2:0] done_cmd_i;

CMD_TYPE cmda[10];
CMD_TYPE cmdq[$];
reg [31:0] qidx;
integer cmdcnt = 0;

initial begin
   $fsdbDumpvars;
   idx = 0;
   clk = 0;
   rst = 1;
   qidx = 0;
   out_of_order_mode = 1;
   #500 rst = 0;
   #2500  $display("done!");
   foreach(cmda[tmp])
      $display("cmda[%d] is %h \n", tmp, cmda[tmp]);
   $display("cmdcnt is %d \n", cmdcnt);
   $display("cmdq has this many elements %d \n", cmdq.size());
   foreach(cmdq[tmp])
      $display("cmdq[%d] is %h \n", tmp, cmdq[tmp]);
   $display("cmdcnt is %d \n", cmdcnt);
 
   $finish;
   $display("won't see this post finish!");
end

always
   #50 clk = ~clk;
   
always @(posedge clk)  begin
   if (rst == 1)  begin
      vld_o <= 0;
      rdy_o <= 0;
      cmd_o <= 0;
      opd1_o <= 0;
      opd2_o <= 0;
      done_i <= 0;
      done_cmd_i <= 0;
   end
   else begin 
      rdy_o <= rdy[idx];
      vld_o <= vld[idx];
      cmd_o <= cmd[idx];
      opd1_o <= opd1[idx];
      opd2_o <= opd2[idx];
      done_i <= done[idx];
      done_cmd_i <= done_cmd[idx];
      idx <= idx + 1; 
   end
end



property p_rdy_done;
   @(posedge clk)
      $rose(rdy_o)  |-> ##[0:$] (done_i == 1);
endproperty

a_rdy_done: assert property (p_rdy_done);


property p_vld_rdy_latency;
   @(posedge clk)
      $rose(vld_o)  |-> ##[1:`LATENCY] (rdy_o == 1);
endproperty

a_vld_rdy_latency: assert property (p_vld_rdy_latency);


property p_vld_rdy;
   @(posedge clk)
      $rose(vld_o)  |-> ##[1:$] (rdy_o == 1);
endproperty

a_vld_rdy: assert property (p_vld_rdy);

property p_no_two_same_cmd;
   @(posedge clk)
      $rose(vld_o)  |-> (cmd_o !== $past(cmd_o)); 
endproperty


a_no_two_same_cmd: assert property(p_no_two_same_cmd);


always @(posedge vld_o or posedge done_i) begin
    if(vld_o == 1)
       cmdcnt = cmdcnt+1;
    else
    if (done_i == 1)
       cmdcnt = cmdcnt-1;
    $display("vld_o or done_i triggered in cmdcnt = %d \n", cmdcnt);
end

property p_no_hlt_if_cmds_out;
   @(posedge clk)
      (cmd_o == HLT) |-> (cmdcnt == 0);
endproperty

a_no_hlt_if_cmds_out: assert property(p_no_hlt_if_cmds_out);

always @(posedge vld_o or posedge done_i) begin
   if (vld_o == 1) begin
      $display("adding %h to qidx=%d \n", cmd_o, qidx);
      cmda[qidx] = cmd_o;
      cmdq.push_front(cmd_o);
      qidx = qidx + 1;
   end
   else if (done_i == 1) begin
      cmdq.pop_front();
   end
   else
      vld_o <= 1'bX;
end

property p_done_eventually;
   @(posedge clk)
      (cmd_o == HLT) |-> (cmdcnt == 0);
endproperty

property p_cmd_done_cmd;
   @(posedge clk)
      (done_i == 1 && out_of_order_mode == 1  ) |-> ( done_cmd_i == cmda[0] || done_cmd_i == cmda[1] || done_cmd_i == cmda[2] || done_cmd_i == cmda[3] || done_cmd_i == cmda[4] || done_cmd_i == cmda[5] || done_cmd_i == cmda[6] || done_cmd_i == cmda[7] || done_cmd_i == cmda[8] || done_cmd_i == cmda[9] || done_cmd_i == cmda[10] );
endproperty


a_cmd_done_cmd: assert property (p_cmd_done_cmd);

endmodule
