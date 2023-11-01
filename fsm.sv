/**fsm.sv
*@info fsm
*
*@brief A simple fsm with the purpose of using it for formal verification training
*
*@details The fsm stage trasision follows the array bellow
*
* q1  q2 | start(00) | odd(01) | even(10) | fin(11)
*-----------------------------------------------------
*  0   0 |   start   |  start  |   start  |  start
*  0   1 |    odd    |  odd    |   odd    |  odd
*  1   0 |   start   |  even   |   start  |  start
*  1   1 |   start   |  start  |   fin    |  fin 
*
* Output --> start: out = 00 , odd: out = 01 , even: out = 10 , fin: out = 11
*/
import fsm_stages_pkg::*; //fsm stages imported from package for easier verification 

module  fsm(
  input  logic clk,
  input  logic reset,
  input  logic q1,
  input  logic q2,
  output logic [1:0] count,
  output c_state state
);




  always_ff @(posedge clk, posedge reset ) begin
  if(reset)begin
      state <= start;
  end
  else
      case(state)
          start : if(!q1 && q2)begin
                     state <= odd;
                  end
          odd   : if(q1 ~^ q2)begin
                     state <= start; 
                  end
                     else if(q1 && !q2)begin
                         state <= even; 
                     end
          even  : if((!q2))begin
                     state <= start;
                  end
                      else if (!q1 && q2)begin
                          state <= odd;
                      end
                          else if(q1 && q2)begin
                              state <= fin;
                          end 
          fin   : if((!q2))begin
                     state <= start;
                  end
                      else if(!q1 && q2)begin
                         state <= odd;
                      end                 
      endcase
  end
  
  always_comb begin
      case(state)
          start : count = 2'b00;
          odd   : count = 2'b01;
          even  : count = 2'b10;
          fin   : count = 2'b11;
      endcase
  end

endmodule