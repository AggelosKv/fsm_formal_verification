module fsm_tb;

import fsm_stages_pkg::*;

logic clk,reset,q1,q2;
logic [1:0] count;
int successful_count;
c_state state;


fsm fsm1 (.clk(clk), .reset(reset), .q1(q1), .q2(q2), .count(count) , .state(state)); // fsm instantiation

bind fsm : fsm1 fsm_assertions sva (.clk(clk), .reset(reset), .q1(q1), .q2(q2), .count(count) , .state(state)); 
// bind fsm instantiation with the assetions module : fsm_assertions

//generate clock signal
always begin
  clk = 1;
  #1ns;
  clk = 0;
  #1ns;
end


initial begin

    successful_count = 0;

    rst;//task reset

    $display("The simulation has started.");

    
    repeat(500) begin
        randcase
            10   : rst;
            1    : begin q1 = 0; q2 = 0; end
            50   : begin q1 = 0; q2 = 1; end
            50   : begin q1 = 1; q2 = 0; end
            50   : begin q1 = 1; q2 = 1; end
        endcase

        if(count == 2'b11)
            successful_count = successful_count + 1;

        @(posedge clk);
    end

    $display ("The fsm made to the end %0d times!",successful_count); // display how many time the output was 2b'11

    repeat(5)
    @(posedge clk);

    $stop();

end

//This task resets the fsm
task rst();
    reset = 1;
    @(posedge clk);
    reset = 0;
endtask


endmodule