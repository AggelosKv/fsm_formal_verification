// This file contains a list of Verilog or SystemVerilog files
// use with the -f option to compile the exercise
//
// Commands to compile and simulate SystemVerilog 
// -----------------------------------------
// Cadence Incisive:          irun -f files.f
// Mentor Graphics QuestaSim: qverilog -f files.f
// Synopsys VCS:              vcs -R -sverilog -f files.f
// For 64-bit  VCS:           vcs -R -sverilog -full64 +acc -f files.f
// Aldec Riviera:             vsimsa -do "alib work; alog -f files.f; asim; run -all; quit"
//
// Commands to compile and simulate SystemVerilog in the gui:
// -----------------------------------------
// Cadence Incisive:          irun +access+rwc -gui -f files.f 
// Mentor Graphics QuestaSim: qverilog -novopt -gui -f files.f
// Synopsys VCS:              vcs -R -sverilog +acc -gui -f files.f
// For 64-bit  VCS:           vcs -R -sverilog -full64 +acc -gui -f files.f
// Aldec Riviera:             riviera -do "alib work; alog -dbg -O0 -f files.f; asim -dbg +access +r"
//
// Optional flags
// -----------------------------------------
// Cadence Incisive:          -q     suppresses certain messages during compilation
// Mentor Graphics QuestaSim: -quiet suppresses certain messages during compilation
// Mentor Graphics QuestaSim: -sv    interprets .v files as containing SystemVerilog code
// Synopsys VCS:              -quiet suppresses certain messages during compilation
// 
// Files to compile
// ----------------

fsm_pkg.sv
fsm.sv
fsm_tb.sv
fsm_assertions.sv

