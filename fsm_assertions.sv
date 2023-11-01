/**fsm_assertions.sv
*@info fsm_assertions
*
*@brief this is the module that contain all the concurrent assertions for verification 
*/


//*******************//
// Macro Definitions //
//*******************//

  `define assertion_check(signal, clock = clk, reset_signal = reset, dis = 0, body)\
  property  check_``signal``_assertion; \
    @(posedge clock) \
    disable iff (reset_signal || dis) \
    body;\
  endproperty \
  assert property (check_``signal``_assertion);


//******************//
// Type Definitions //
//******************//

import fsm_stages_pkg::*; //import the fsm stages from package for easier verification


module fsm_assertions(
  input logic clk,
  input logic reset,
  input logic q1,
  input logic q2,
  input logic [1:0] count,
  input c_state state
);



//covergroup

  covergroup cvr_counter @(clk  iff !reset);
    option.per_instance = 1;


    count_cp  : coverpoint count {
      bins start = {2'b00};
      bins odd   = {2'b01};
      bins even  = {2'b10}; 
      bins fin   = {2'b11};    
    }

  endgroup

//**********************************************************//
//                                                          //
// Checking the transition from one stage to the next stage //
//                                                          //
//**********************************************************//

//reset
  `assertion_check(reset_fsm,,0,, reset |-> (count == 2'b00));

//start

  `assertion_check(start_to_odd,,,, ( state == start ) && $rose(!q1 && q2 ) |=> state == odd );  //$rose is there to resolve an assertion error for a case when reset==1 and the property is true for 2 cycles
  
  `assertion_check(start_to_start,,,, ( state == start ) && (!(!q1 && q2 )) |=> state == start );

//odd

  `assertion_check(odd_to_even,,,, ( state == odd ) && (q1 && !q2 ) |=> state == even );

  `assertion_check(odd_to_start,,,, ( state == odd ) && (q1 ~^ q2 ) |=> state == start );

  `assertion_check(odd_to_odd,,,, ( state == odd ) && (!q1 && q2) |=> state == odd );

//even
  
  `assertion_check(even_to_fin,,,, ( state == even ) && (q1 && q2) |=> state == fin );
  
  `assertion_check(even_to_start,,,, ( state == even ) && ((!q2)) |=> state == start );
  
  `assertion_check(even_to_odd,,,, ( state == even ) && ((!q1 && q2)) |=> state == odd );

//fin   

  `assertion_check(fin_to_fin,,,, (( state == fin ) && (q1 && q2)) |=> state == fin );

  `assertion_check(fin_to_start,,,, (( state == fin ) && (!q2)) |=> state == start );

  `assertion_check(fin_to_odd,,,, (( state == fin ) && (!q1 && q2)) |=> state == odd );   


//*********************************************************//
//                                                         //
// Checking the transition to a stage from previous stages //
//                                                         //
//*********************************************************//

//start
  
  `assertion_check(start_from_start,,,, (count == start ) && $past(count == start) && $past(!reset) && !reset|-> $past(!(!q1 && q2) ) );
  
  `assertion_check(start_from_odd,,,, (count == start ) && $past(count == odd) && !reset |-> $past(q1 ~^ q2) );
  
  `assertion_check(start_from_even,,,, (count == start ) && $past(count == even) && !reset |-> $past(!q2) );
  
  `assertion_check(start_from_fin,,,, (count == start ) && $past(count == fin) && !reset |-> $past(!q2) );
    
//odd

  `assertion_check(odd_from_start,,,, (count == odd ) && $past(count == start) && !reset |-> $past(!q1 && q2) );

  `assertion_check(odd_from_odd,,,, (count == odd ) && $past(count == odd) |-> $past(!q1 && q2) );

  `assertion_check(odd_from_even,,,, (count == odd ) && $past(count == even) |-> $past(!q1 && q2) );

  `assertion_check(odd_from_fin,,,, (count == odd ) && $past(count == fin) |-> $past(!q1 && q2) );

//even

`assertion_check(even_from_odd,,,, (count == even ) && $past(count == odd) |-> $past(q1 && !q2) );

//fin

  `assertion_check(fin_from_even,,,, (count == fin ) && $past(count == even) |-> $past(q1 && q2) );

  `assertion_check(fin_from_fin,,,, (count == fin ) && $past(count == fin) |-> $past(q1 && q2) );

endmodule
