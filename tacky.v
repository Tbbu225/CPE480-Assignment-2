// basic sizes of things
`define Word	[15:0]
`define HalfWord[7:0]
`define Opcode  [4:0]
`define Opcode1	[15:11]
`define Opcode2 [7:3]
`define Reg     [2:0]
`define Reg1    [10:8]
`define Reg2    [2:0]
`define Imm8    [7:0]
`define RegSize [16:0]
`define RegNum  [7:0]
`define RegType [16]
`define RegValue[15:0]
`define MemSize [65535:0]
`define Acc0    [0]
`define Acc1    [1]
`define NumReg  8

// opcode values
`define OPnot	5'b00000
`define OPand	5'b00001
`define OPor	5'b00010
`define OPxor	5'b00011
`define OPadd	5'b00100
`define OPsub	5'b00101
`define OPmul	5'b00110
`define OPdiv	5'b00111
`define OPsh	5'b01000
`define OPslt	5'b01001
`define OPcvt 	5'b01010
`define OPlf	5'b01011
`define OPli	5'b01100
`define OPr2a	5'b01101
`define OPa2r	5'b01110
`define OPst	5'b01111
`define OPjr    5'b10000
`define OPjnz8  5'b11001
`define OPjz8   5'b11010
`define OPjp8   5'b11011
`define OPcf8   5'b11100
`define OPci8   5'b11101
`define OPpre   5'b11110
`define OPsys   5'b11111

//Bit value for float vs int registers
`define Float   1'b1
`define Int     1'b0

//Control signal channels
`define Signal          [3:0]
`define J_8_Compare     [1:0]
`define Reg_Value       [2]
`define Jr_Load         [3]
`define PCinc           2'b00
`define Reg_is_0        2'b01
`define Reg_is_not_0    2'b10
`define UseImm8         2'b11
`define Jr_None         2'b00
`define Jr_Reg1         2'b10
`define Jr_Reg2         2'b11

//PC and jump logic
module tacky_jump(pc, op1, op2, immediate, reg1, reg2, clk, reset);
output reg `Word pc; 
input `Word reg1, reg2, immediate; input `Opcode op1, op2; input clk, reset;

reg `Signal signal;
wire `Word next_pc;

initial 
begin
    pc = 0;
    signal = 0;
end

counter count(next_pc, immediate, reg1, reg2, signal, pc);

always @(op1, op2) 
begin
    if(op1 == `OPjp8)                           signal = {`Jr_None, `UseImm8};
    else if(op1 == `OPjz8)                      signal = {`Jr_None, `Reg_is_0};
    else if(op1 == `OPjnz8)                     signal = {`Jr_None, `Reg_is_not_0};
    else if(op1 == `OPjr)                       signal = {`Jr_Reg1, `PCinc};
    else if(op1 < `OPjr && op2 == `OPjr)        signal = {`Jr_Reg2, `PCinc};
    else                                        signal = {`Jr_None, `PCinc};
end

always @(posedge clk) 
begin
    if(!reset) pc <= next_pc;
    else pc <= 0;
end

endmodule

//Incrementer for pc
module incrementer(newpc, pc);
    output `Word newpc; 
    input `Word pc; 
    
    assign newpc = pc + 1;
endmodule


//Compare to see if a register value is or is not 0, as well as directly set the result if needed. 
//Used for jnz8, jp8, and jz8 (2b'00 is for none of them).
module compare_to_0(result, value, condition);
output reg result; 
input `Word value; input [1:0] condition;

always @(*)
    case(condition)
        `PCinc: result = 0;
        `Reg_is_0: result = value == 0;
        `Reg_is_not_0: result = value != 0;
        `UseImm8: result = 1;
    endcase
endmodule

//circuit which decides next value of pc
//Signal bits:
//[1:0]: decide whether to use load incremeted pc or {pre, immediate}
//[2]: decide which register to use for jr 
//[3]: decide between previous pc decision result and register value for pc (if[1:0] non-zero, should always be 0)
module counter(new_pc, immediate, reg1, reg2, control_logic, pc);
output `Word new_pc;
input `Signal control_logic; input `Word reg1, reg2, immediate, pc;
wire `Word pc_inc, pc_inc_vs_immediate, pc_result, reg1_vs_reg2;  
wire compare_result;

incrementer inc(pc_inc, pc);
compare_to_0 compare(compare_result, reg1, control_logic `J_8_Compare);
assign pc_inc_vs_immediate = (compare_result) ? immediate : pc_inc;
assign reg1_vs_reg2 = (control_logic `Reg_Value) ? reg2 : reg1;
assign pc_result = (control_logic `Jr_Load) ?  reg1_vs_reg2 : pc_inc_vs_immediate;
assign new_pc = pc_result;

endmodule

module tacky_halt(halt, op1);
output halt;
input `Opcode op1;

assign halt = (op1 == `OPsys) ? 1'b1 : 1'b0; 

endmodule

//Instruction memory
module tacky_instruction_mem(instruction, pc, reset);
output `Word instruction; 
input `Word pc; input reset;

reg `Word memory `MemSize;

initial 
begin
    $readmemh0(memory);
end

assign instruction = memory [pc];

always @ (posedge reset) 
begin
    $readmemh0(memory);
end

endmodule

//Register file. Handles determining which values to load based on current opcode(s). 
module tacky_register_file(pre_value, reg1_value, reg2_value, r0_value, r1_value, reg1, reg2, Imm8_to_pre, r0Str, r1Str, RegStr_Imm16, DataStr1, DataStr2, op1, op2, clk, reset);

output `RegSize reg1_value, reg2_value, r0_value, r1_value; //values for registers in instructions, as well as $0 and $1
output `HalfWord pre_value;                                 //value of pre register
input `Reg reg1, reg2;                                      //value coressponding to register number to access in instruction
input `Imm8 Imm8_to_pre;                                    //direct connection 8bit immediate to pre register (for pre instruction)
input `RegSize r0Str, r1Str;                                //results to be stored from ALU
input `Word RegStr_Imm16, DataStr1, DataStr2;               //results to be stored from an immediate value or from data memory
input `Opcode1 op1, op2;                                    //opcodes in instruction
input clk, reset;

reg `RegSize registers `RegNum;
reg `HalfWord pre;

integer i;

initial 
begin
    for (i = 0; i < `NumReg; i = i + 1)
    begin
        registers[i] = 0;
    end
    pre = 0;
end

assign reg1_value = registers[reg1];
assign reg2_value = registers[reg2];
assign r0_value = registers`Acc0;
assign r1_value = registers`Acc1;
assign pre_value = pre;

always @(negedge clk)
begin
    //ALU operations
    if(op1 <= `OPslt) registers `Acc0 <= r0Str;
    if(op1 <= `OPjr && op2 <= `OPslt) registers `Acc1 <= r1Str;
    
    //Pre
    if(op1 == `OPpre) pre <= Imm8_to_pre;
    
    //Load immediate
    if(op1 == `OPcf8) registers[reg1] <= {`Float, RegStr_Imm16};
    if(op1 == `OPci8) registers[reg1] <= {`Int, RegStr_Imm16};
    
    //Load from memory
    if(op1 == `OPlf) registers[reg1] <= {`Float, DataStr1}; 
    if(op1 <= `OPjr && op2 == `OPlf) registers[reg2] <= {`Float, DataStr2};
    if(op1 == `OPli) registers[reg1] <= {`Int, DataStr1};
    if(op1 <= `OPjr && op2 == `OPli) registers[reg2] <= {`Int, DataStr2};
    
    //Accumulator <-> register
    if(op1 == `OPa2r) registers[reg1] <= registers`Acc0;
    if(op1 <= `OPjr && op2 == `OPa2r) registers[reg2] <= registers`Acc1;
    if(op1 == `OPr2a) registers`Acc0 <= registers[reg1];
    if(op1 <= `OPjr && op2 == `OPr2a) registers`Acc1 <= registers[reg2];
end

always @(posedge reset) 
begin
    for (i = 0; i < `NumReg; i = i + 1)
    begin
        registers[i] = 0;
    end
    pre = 0;
end

endmodule 

//External module which prepends pre register to immediate value in instruction.
//Ignored if not needed.
module tacky_prepend(Imm16, pre, Imm8);
    output `Word Imm16;
    input `HalfWord pre, Imm8;
    assign Imm16 = {pre, Imm8};
endmodule


//Data memory
module tacky_data_mem(reg1Str, reg2Str, op1, op2, reg1, reg2, r0, r1, reset);
output reg `Word reg1Str, reg2Str;      //Values to store in register file 
input `Word reg1, reg2, r0, r1;     //values of registers specifed from instructions
input `Opcode op1, op2;             //opcode values in instructions
input reset;

reg `Word memory `MemSize;

initial 
begin
    $readmemh1(memory);
end

always @(op1 or op2 or reg1 or reg2 or r0 or r1)
begin
    if(op1 == `OPst) memory[reg1] = r0;
    if(op1 <= `OPjr && op2 == `OPst) memory[reg2] = r1;
    if(op1 == `OPlf || op1 == `OPli) reg1Str = memory[r0];
    if(op1 <= `OPjr && (op2 == `OPlf || op2 == `OPli) ) reg2Str = memory[r1];
end


always @ (posedge reset) 
begin
    $readmemh1(memory);
end

endmodule

// Floating point Verilog modules for CPE480
// Created February 19, 2019 by Henry Dietz, http://aggregate.org/hankd
// Distributed under CC BY 4.0, https://creativecommons.org/licenses/by/4.0/

// Field definitions
`define	WORD	[15:0]	// generic machine word size
`define	INT	signed [15:0]	// integer size
`define FLOAT	[15:0]	// half-precision float size
`define FSIGN	[15]	// sign bit
`define FEXP	[14:7]	// exponent
`define FFRAC	[6:0]	// fractional part (leading 1 implied)

// Constants
`define	FZERO	16'b0	  // float 0
`define F32767  16'h46ff  // closest approx to 32767, actually 32640
`define F32768  16'hc700  // -32768

// Count leading zeros, 16-bit (5-bit result) d=lead0s(s)
module lead0s(d, s);
output wire [4:0] d;
input wire `WORD s;
wire [4:0] t;
wire [7:0] s8;
wire [3:0] s4;
wire [1:0] s2;
assign t[4] = 0;
assign {t[3],s8} = ((|s[15:8]) ? {1'b0,s[15:8]} : {1'b1,s[7:0]});
assign {t[2],s4} = ((|s8[7:4]) ? {1'b0,s8[7:4]} : {1'b1,s8[3:0]});
assign {t[1],s2} = ((|s4[3:2]) ? {1'b0,s4[3:2]} : {1'b1,s4[1:0]});
assign t[0] = !s2[1];
assign d = (s ? t : 16);
endmodule

// Float set-less-than, 16-bit (1-bit result) torf=a<b
module fslt(torf, a, b);
output wire torf;
input wire `FLOAT a, b;
assign torf = (a `FSIGN && !(b `FSIGN)) ||
	      (a `FSIGN && b `FSIGN && (a[14:0] > b[14:0])) ||
	      (!(a `FSIGN) && !(b `FSIGN) && (a[14:0] < b[14:0]));
endmodule

// Floating-point addition, 16-bit r=a+b
module fadd(r, a, b);
output wire `FLOAT r;
input wire `FLOAT a, b;
wire `FLOAT s;
wire [8:0] sexp, sman, sfrac;
wire [7:0] texp, taman, tbman;
wire [4:0] slead;
wire ssign, aegt, amgt, eqsgn;
assign r = ((a == 0) ? b : ((b == 0) ? a : s));
assign aegt = (a `FEXP > b `FEXP);
assign texp = (aegt ? (a `FEXP) : (b `FEXP));
assign taman = (aegt ? {1'b1, (a `FFRAC)} : ({1'b1, (a `FFRAC)} >> (texp - a `FEXP)));
assign tbman = (aegt ? ({1'b1, (b `FFRAC)} >> (texp - b `FEXP)) : {1'b1, (b `FFRAC)});
assign eqsgn = (a `FSIGN == b `FSIGN);
assign amgt = (taman > tbman);
assign sman = (eqsgn ? (taman + tbman) : (amgt ? (taman - tbman) : (tbman - taman)));
lead0s m0(slead, {sman, 7'b0});
assign ssign = (amgt ? (a `FSIGN) : (b `FSIGN));
assign sfrac = sman << slead;
assign sexp = (texp + 1) - slead;
assign s = (sman ? (sexp ? {ssign, sexp[7:0], sfrac[7:1]} : 0) : 0);
endmodule

// Floating-point multiply, 16-bit r=a*b
module fmul(r, a, b);
output wire `FLOAT r;
input wire `FLOAT a, b;
wire [15:0] m; // double the bits in a fraction, we need high bits
wire [7:0] e;
wire s;
assign s = (a `FSIGN ^ b `FSIGN);
assign m = ({1'b1, (a `FFRAC)} * {1'b1, (b `FFRAC)});
assign e = (((a `FEXP) + (b `FEXP)) -127 + m[15]);
assign r = (((a == 0) || (b == 0)) ? 0 : (m[15] ? {s, e, m[14:8]} : {s, e, m[13:7]}));
endmodule

// Floating-point reciprocal, 16-bit r=1.0/a
// Note: requires initialized inverse fraction lookup table
module frecip(r, a);
output wire `FLOAT r;
input wire `FLOAT a;
reg [6:0] look[127:0];
initial $readmemh2(look);
assign r `FSIGN = a `FSIGN;
assign r `FEXP = 253 + (!(a `FFRAC)) - a `FEXP;
assign r `FFRAC = look[a `FFRAC];
endmodule

// Floating-point shift, 16 bit
// Shift +left,-right by integer
module fshift(r, f, i);
output wire `FLOAT r;
input wire `FLOAT f;
input wire `INT i;
assign r `FFRAC = f `FFRAC;
assign r `FSIGN = f `FSIGN;
assign r `FEXP = (f ? (f `FEXP + i) : 0);
endmodule

// Integer to float conversion, 16 bit
module i2f(f, i);
output wire `FLOAT f;
input wire `INT i;
wire [4:0] lead;
wire `WORD pos;
assign pos = (i[15] ? (-i) : i);
lead0s m0(lead, pos);
assign f `FFRAC = (i ? ({pos, 8'b0} >> (16 - lead)) : 0);
assign f `FSIGN = i[15];
assign f `FEXP = (i ? (128 + (14 - lead)) : 0);
endmodule

// Float to integer conversion, 16 bit
// Note: out-of-range values go to -32768 or 32767
module f2i(i, f);
output wire `INT i;
input wire `FLOAT f;
wire `FLOAT ui;
wire tiny, big;
fslt m0(tiny, f, `F32768);
fslt m1(big, `F32767, f);
assign ui = {1'b1, f `FFRAC, 16'b0} >> ((128+22) - f `FEXP);
assign i = (tiny ? 0 : (big ? 32767 : (f `FSIGN ? (-ui) : ui)));
endmodule

module sh(out, a, b); //out = a >> b (b positive) or a << b (b negative)
input signed `RegValue a, b;
output `RegValue out;
wire `INT flip = 0-b;
assign out = ((b>=0) ? (a >> b) : (a << flip));
endmodule


//ALU unit
module tacky_ALU(resultout, op, acc, regIn);
output reg `RegSize resultout;
input `Opcode op;
input `RegSize acc, regIn;
wire `INT accValue = acc `RegValue, regInValue = regIn `RegValue;
wire `FLOAT floatAdd, floatRecip, floatMul, floatSub, floatDiv;
wire `RegValue shifted;
wire setLess;

fslt floatslt(setLess, acc `RegValue, regIn `RegValue);
sh shift(shifted, accValue, regInValue); 
fadd floatadd(floatAdd, acc `RegValue, regIn `RegValue);
fadd floatsub(floatSub, acc `RegValue, regIn `RegValue);
frecip floatrecip(floatRecip, regIn `RegValue);
fmul floatmul(floatMul, acc `RegValue, regIn `RegValue);
fmul floatdiv(floatDiv, acc `RegValue, floatRecip `RegValue);

wire `INT intC, floatC;
f2i floatreg(intC, regIn `RegValue);
i2f intreg(floatC, regIn `RegValue);

always @(*)
begin
    casez ({acc `RegType, op})
        {`Float, `OPadd}: resultout = {acc `RegType, floatAdd};
        {`Float, `OPsub}: resultout = {acc `RegType, floatSub};
        {`Float, `OPmul}: resultout = {acc `RegType, floatMul};
        {`Float, `OPdiv}: resultout = {acc `RegType, floatDiv};
        {`Float, `OPcvt}: resultout = {`Int, intC};
        {`Int, `OPcvt}: resultout = {`Float, floatC};
        {`Int, `OPadd}: resultout ={acc `RegType,  (accValue + regInValue)};
        {`Int, `OPsub}: resultout = {acc `RegType, (accValue - regInValue)};
        {`Int, `OPmul}: resultout = {acc `RegType, (accValue * regInValue)};
        {`Int, `OPdiv}: resultout = {acc `RegType, (accValue / regInValue)};
        {1'b?, `OPand}: resultout = {acc `RegType, (accValue & regInValue)};
        {1'b?, `OPor} : resultout = {acc `RegType, (accValue | regInValue)};
        {1'b?, `OPxor}:resultout = {acc `RegType, (accValue ^ regInValue)};
        {1'b?, `OPnot}: resultout = {acc `RegType, (~accValue)};
        {1'b?, `OPsh}: resultout = {acc `RegType, shifted};
        {`Float, `OPslt}: resultout = {`Int, setLess};
        {`Int, `OPslt}: resultout = {`Int, accValue < regInValue };
        default: resultout = acc;
    endcase
end 
endmodule

//Complete processor
module tacky_processor(halt, reset, clk);
output halt;
input reset, clk;

wire `Word instruction_bus, pc_bus, immediate_bus, mem1_bus, mem2_bus;
wire `RegSize reg1_bus, reg2_bus, r0_bus, r1_bus, ALU1_bus, ALU2_bus;
wire `HalfWord pre_bus;

tacky_jump pc_jump(pc_bus, instruction_bus `Opcode1, instruction_bus `Opcode2, immediate_bus, reg1_bus `RegValue, reg2_bus `RegValue, clk, reset); //PC+jump logic
tacky_prepend pre_imm(immediate_bus, pre_bus, instruction_bus `Imm8); //Component to prepend pre with an immediate value
tacky_halt halter(halt, instruction_bus `Opcode1); //Halt signal
tacky_instruction_mem instr_mem(instruction_bus, pc_bus, reset); //memory for instructions
tacky_register_file regfile(pre_bus, reg1_bus, reg2_bus, r0_bus, r1_bus, instruction_bus `Reg1, instruction_bus `Reg2, instruction_bus `Imm8, ALU1_bus, ALU2_bus, immediate_bus, mem1_bus, mem2_bus, instruction_bus `Opcode1, instruction_bus `Opcode2, clk, reset); //register file
tacky_ALU alu1(ALU1_bus, instruction_bus `Opcode1, r0_bus, reg1_bus); //ALU for first instruction
tacky_ALU alu2(ALU2_bus, instruction_bus `Opcode2, r1_bus, reg2_bus); //ALU for second instruction (if needed)
tacky_data_mem data_mem(mem1_bus, mem2_bus, instruction_bus `Opcode1, instruction_bus `Opcode2, reg1_bus `RegValue, reg2_bus `RegValue, r0_bus `RegValue, r1_bus `RegValue, reset); //data memory
endmodule


module testbench;
reg reset = 0;
reg clk = 0;
wire halted;

tacky_processor PE(halted, reset, clk);

initial begin
  $dumpfile;
  $dumpvars(0, PE);
  #10 reset = 1;
  #10 reset = 0;
  while (!halted) begin
    #1 clk = 1;
    #1 clk = 0;
  end
  $finish;
end

initial begin
    #(10**10) $finish;
end

endmodule
