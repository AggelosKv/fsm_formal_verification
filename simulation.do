quit -sim
file delete -force work

vlib work
vlog -f files.f

vsim -lib work -gui -assertdebug fsm_tb -appendlog -l qverilog.log -novopt -prevmsgcount 0,0,0,0 -usestarttime 8,52,19,26,9,123,4,298,1


add wave {fsm_tb/clk}
add wave {fsm_tb/reset}
add wave {fsm_tb/q1}
add wave {fsm_tb/q2}
add wave {fsm_tb/count}
add wave {fsm_tb/fsm1/state}

radix -binary

run -all

