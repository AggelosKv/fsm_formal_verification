/**fsm_assertions.sv
*@info fsm_assertions
*
*@brief this is the module that contain all the concurrent assertions for verification 
*/
module fsm_assertions(
  input logic clk,
  input logic reset,
  input logic q1,
  input logic q2,
  input logic [1:0] count
);

//**********************************************************//
//                                                          //
// Checking the transition from one stage to the next stage //
//                                                          //
//**********************************************************//

//reset
  property reset_fsm;
      reset |-> (count == 2'b00);
  endproperty

  reset_fsm_Assertion     : assert property (@(posedge clk) reset_fsm );

//start
  property start_to_odd;
      (( count == 2'b00 ) && $rose(!q1 && q2 )) |=> count == 2'b01;
  endproperty
  
  start_to_odd_assertion : assert property (@(posedge clk) disable iff (reset) start_to_odd);


  property start_to_start;
      (( count == 2'b00 ) && (!(!q1 && q2 ))) |=> count == 2'b00;
  endproperty
  
  start_to_start_assertion : assert property (@(posedge clk) disable iff (reset) start_to_start);

//odd
  property odd_to_even;
      (( count == 2'b01 ) && $rose(q1 && !q2 )) |=> count == 2'b10;
  endproperty
  
  odd_to_even_assertion : assert property (@(posedge clk) disable iff (reset) odd_to_even);


  property odd_to_start;
      (( count == 2'b01 ) && (q1 ~^ q2 )) |=> count == 2'b00;
  endproperty
  
  odd_to_start_assertion : assert property (@(posedge clk) disable iff (reset) odd_to_start);


  property odd_to_odd;
      (( count == 2'b01 ) && (!q1 && q2)) |=> count == 2'b01;
  endproperty
  
  odd_to_odd_assertion : assert property (@(posedge clk) disable iff (reset) odd_to_odd);

//even
  property even_to_fin;
      (( count == 2'b10 ) && (q1 && q2)) |=> count == 2'b11;
  endproperty
  
  even_to_fin_assertion : assert property (@(posedge clk) disable iff (reset) even_to_fin);


  property even_to_start;
      (( count == 2'b10 ) && (!q2)) |=> count == 2'b00;
  endproperty
  
  even_to_start_assertion : assert property (@(posedge clk) disable iff (reset) even_to_start);


  property even_to_odd;
      (( count == 2'b10 ) && (!q1 && q2)) |=> count == 2'b01;
  endproperty
  
  even_to_odd_assertion : assert property (@(posedge clk) disable iff (reset) even_to_odd);

//fin
  property fin_to_fin;
      (( count == 2'b11 ) && (q1 && q2)) |=> count == 2'b11;
  endproperty
  
  fin_to_fin_assertion : assert property (@(posedge clk) disable iff (reset) fin_to_fin);


  property fin_to_start;
      (( count == 2'b11 ) && (!q2)) |=> count == 2'b00;
  endproperty
  
  fin_to_start_assertion : assert property (@(posedge clk) disable iff (reset) fin_to_start);

  property fin_to_odd;
      (( count == 2'b11 ) && (!q1 && q2)) |=> count == 2'b01;
  endproperty
  
  fin_to_odd_assertion : assert property (@(posedge clk) disable iff (reset) fin_to_odd);


//*********************************************************//
//                                                         //
// Checking the transition to a stage from previous stages //
//                                                         //
//*********************************************************//

//start
  property start_from_start;
       (count == 2'b00 ) && $past(count == 2'b00) && !reset && $past(!reset) |-> $past(!(!q1 && q2) ) ;
  endproperty
  
  start_from_start_destinetion_assertion : assert property (@(posedge clk) disable iff (reset) start_from_start);


  property start_from_odd;
       (count == 2'b00 ) && $past(count == 2'b01) && !reset |-> $past(q1 ~^ q2)  ;
  endproperty
  
  start_from_odd_destinetion_assertion : assert property (@(posedge clk) disable iff (reset) start_from_odd);

  
  property start_from_even;
       (count == 2'b00 ) && $past(count == 2'b10) && !reset |-> $past(!q2) ;
  endproperty
  
  start_from_even_destinetion_assertion : assert property (@(posedge clk) disable iff (reset) start_from_even);

  
  property start_from_fin;
       (count == 2'b00 ) && $past(count == 2'b11) && !reset |-> $past(!q2) ;
  endproperty
  
  start_from_fin_destinetion_assertion : assert property (@(posedge clk) disable iff (reset) start_from_fin);


  //odd
    property odd_from_start;
       (count == 2'b01 ) && $past(count == 2'b00)  |-> $past((!q1 && q2) ) ;
  endproperty
  
  odd_from_start_destinetion_assertion : assert property (@(posedge clk) disable iff (reset) odd_from_start);


  property odd_from_odd;
       (count == 2'b01 ) && $past(count == 2'b01) |-> $past(!q1 && q2)  ;
  endproperty
  
  odd_from_odd_destinetion_assertion : assert property (@(posedge clk) disable iff (reset) odd_from_odd);

  
  property odd_from_even;
       (count == 2'b01 ) && $past(count == 2'b10) |-> $past(!q1 && q2) ;
  endproperty
  
  odd_from_even_destinetion_assertion : assert property (@(posedge clk) disable iff (reset) odd_from_even);

  
  property odd_from_fin;
       (count == 2'b01 ) && $past(count == 2'b11) |-> $past(!q1 && q2) ;
  endproperty
  
  odd_from_fin_destinetion_assertion : assert property (@(posedge clk) disable iff (reset) odd_from_fin);


  //even
  property even_from_odd;
       (count == 2'b10 ) && $past(count == 2'b01) |-> $past(q1 && !q2) ;
  endproperty
  
  even_from_odd_destinetion_assertion : assert property (@(posedge clk) disable iff (reset) even_from_odd);

  //fin
  property fin_from_even;
       (count == 2'b11 ) && $past(count == 2'b10) |-> $past(q1 && q2) ;
  endproperty
  
  fin_from_even_destinetion_assertion : assert property (@(posedge clk) disable iff (reset) fin_from_even);


  property fin_from_fin;
       (count == 2'b11 ) && $past(count == 2'b11) |-> $past(q1 && q2) ;
  endproperty
  
  fin_from_fin_destinetion_assertion : assert property (@(posedge clk) disable iff (reset) fin_from_fin);

endmodule
