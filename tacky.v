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
`define NumReg  8
`define Acc0    [0]
`define Acc1    [1]

// opcode values, also state numbers
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

//Register values
`define r0 3'd0
`define r1 3'd1
`define r2 3'd2
`define r3 3'd3
`define r4 3'd4
`define ra 3'd5
`define rv 3'd6
`define sp 3'd7

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
module tacky_jump(pc, op1, op2, immediate, reg1, reg2, clk, reset, halt);
output reg `Word pc; 
input `Word reg1, reg2, immediate; input `Opcode op1, op2; input clk, reset, halt;

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
    if( !(reset || halt) ) pc <= next_pc;
    else if (!halt) pc <= 0;
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

module tacky_halt(halt, op1, reset);
output halt, reset;
input `OPcode op1;

assign halt = (op1 == `OPSys && !reset) ? 1'b1 : 1'b0; 

endmodule

/*
//test for pc and jump logic
module test_control;
reg `Word reg1, reg2, immediate; reg `Opcode op1, op2; reg clk;
wire `Word pc;

tacky_jump jump(pc, op1, op2, immediate, reg1, reg2, clk);

initial 
begin
    $dumpfile("test-jumps.vcd");
    $dumpvars(0, pc);
    $dumpvars(0, clk);
    $dumpvars(0, jump);
    op1 = `OPadd;
    op2 = `OPadd;
    immediate = 16'h0f0f;
    reg1 = 0;
    reg2 = 1;
    clk = 0;
    #1 while(1) 
    begin
        #1 clk = ~clk;
    end
end

initial 
begin
    #20 op1 = `OPjp8;
    #2 op1 = `OPadd;
    #20 op1 = `OPjnz8;
    #2 op1 = `OPadd;
    #2  reg1 = 1;
    #20 op1 = `OPjnz8;
    #2 op1 = `OPadd;
    #20 op1 = `OPjz8;
    #2 op1 = `OPadd;
    #2 reg1 = 0;
    #20 op1 = `OPjz8;
    #2 op1 = `OPadd;
    #2 reg1 = 16'h0ff0; reg2 = 16'hf00f;
    #20 op1 = `OPjr;
    #2 op1 = `OPadd;
    #20 op1 = `OPadd; op2 = `OPjr;
    #2 op2 = `OPadd;
    #20 $finish;
end
endmodule
*/

/*
module test_jp;
reg `Word pc, reg1, reg2, immediate;
reg `Signal signal;
reg clk = 0;
wire `Word result;

counter count(result, immediate, reg1, reg2, signal, pc);



always @(posedge clk) 
begin
    pc <= result;
end

initial begin
    $dumpfile("test.vcd");
    $dumpvars(0, pc);
    pc = 0;
    reg1 = 16'h00ff;
    reg2 = 16'h0ff0;
    immediate = 16'h1234;
    signal = 4'h0;
    while(pc < 16'hffff) begin
    #1 clk = 1;
    #1 clk = 0;
    end
    $finish;
end

initial begin
    #50 signal = 4'h2;
    #10 signal = 4'h0;
    
    #10 reg1 = 0;
    #10 signal = 4'h1;
    #10 signal = 4'h0;
    #10 reg1 = 16'h00ff;
    
    #1 signal = 4'h3;
    #10 signal = 4'h0;
    
    #10 signal = 4'h8;

    #10 signal = 4'hc;
    
    #10 signal = 4'h0;

end

endmodule
*/

//Instruction memory
module tacky_instruction_mem(instruction, pc, reset);
output `Word instruction; 
input `Word pc; input reset;

reg `Word memory `MemSize;

initial 
begin
    $readmemh("instructions.vmem", memory);
    //$readmemh0(memory);
end

assign instruction = memory [pc];

always @ (posedge reset) 
begin
    $readmemh("instructions.vmem", memory);
    //$readmemh0(memory);
end

endmodule

/*
module test_memory;
reg `Word reg1, reg2, immediate; reg `Opcode op1, op2; reg clk;
wire `Word pc, instruction;


tacky_jump jump(pc, instruction `Opcode1 , instruction `Opcode2, immediate, reg1, reg2, clk);
tacky_instruction_mem instructions(instruction, pc);

initial 
begin
    $dumpfile("test-instruction-mem.vcd");
    $dumpvars(0, pc);
    $dumpvars(0, clk);
    $dumpvars(0, jump);
    $dumpvars(0, instructions);
    immediate = 24;
    reg1 = 0;
    reg2 = 1;
    clk = 0;
    #1 while(1) #1 clk = ~clk;
end

initial 
begin
    #20 reg2 = 8;
    #400 $finish;
end

endmodule
*/

//Register file. Handles determining which values to load based on current opcode(s). 
module tacky_register_file(reg1_value, reg2_value, r0_value, r1_value, reg1, reg2, Imm8_to_pre, r0Str, r1Str, RegStr_Imm16, DataStr1, DataStr2, op1, op2, clk, reset);

output reg `Regsize reg1_value, reg2_value, r0_value, r1_value;
input `Reg reg1, reg2;
input `Imm8 Imm8_to_pre;
input `Word r0Str, r1Str, RegStr_Imm16, DataStr1, DataStr2;
input `Opcode1 op1, op2;
input clk;

reg `RegSize registers `RegNum;
reg `HalfWord pre;

initial 
begin
    for (i = 0; i < `NumReg; i = i + 1)
    begin
        register[i] = 0;
    end
    pre = 0;
end

assign reg1_value = registers[reg1];
assign reg2_value = registers[reg2];
assign r0_value = registers`Acc0;
assign r1_value = registers`Acc1;

always @(negedge clk)
begin
    //ALU operations
    if(op1 <= `OPslt) registers `Acc0 <= r0Str;
    if(op1 <= `OPjr && op2 <= `OPslt) registers `Acc1 <= r1Str;
    
    //Pre
    if(op1 == `OPpre) pre <= Imm8_to_pre;
    
    //Load immediate
    if(op1 == `OPcf8) registers[reg1] <= {`Float, RegStr_Imm16};
    if(op1 == `OPci8) registers[reg1] <= {`In, RegStr_Imm16};
    
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
        register[i] = 0;
    end
    pre = 0;
end

endmodule 

//External module which prepends pre register to immediate value in instruction.
//Ignored if not needed.
module prepend(Imm16, pre, Imm8);
    output `Word Imm16;
    input `HalfWord pre, Imm8;
    assign Imm16 = {pre, Imm8};
endmodule

//Data memory (WIP)
module tacky_data_mem(reg1Str, reg2Str, op1, op2, reg1, reg2, r0, r1);
output `Word reg1Str, reg2Str;
input `Word reg1, reg2, r0, r1; input `Opcode op1, op2;

reg `Word memory `MemSize;

initial 
begin
    $readmemh("data.vmem", memory);
    //$readmemh1(memory);
end

always @(*)
    if(op1 == `OPst) memory[reg1] = r0;
    if(op1 <= `OPjr && op2 == `OPst) memory[reg2] = r1;
    if(op1 == `OPlf || op1 == `OPli) reg1Str = memory[r0];
    if(op1 <= `OPjr && (op2 == `OPlf || op2 == `OPli) ) reg2Str = memory[r1];
begin
    
end

always @ (posedge reset) 
begin
    $readmemh("data.vmem", memory);
    //$readmemh1(memory);
end
endmodule

module sh(out, a, b); //out = a >> b (b positive) or a << b (b negative)
input signed `RegValue a, b;
output `RegValue out;
wire `INT flip = 0-b;
assign out = ((b>=0) ? (a >> b) : (a << flip));
endmodule

module ALU(op, acc, regIn, resultout);
input `Opcode op;
input `RegSize acc, regIn;
output reg `RegSize resultout;
wire `INT accValue = acc `RegValue, regInValue = regIn `RegValue;
wire `FLOAT floatAdd, floatRecip, floatMul, floatSub, floatDiv;
wire `RegValue shifted, setLess;

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
        {1'b?, `OPa2r}: resultout = acc;
        {1'b?, `OPr2a}: resultout = regIn;
        {1'b?, `OPsh}: resultout = {acc `RegType, shifted};
        {`Float, `OPslt}: resultout = {`Int, setLess};
        {`Int, `OPslt}: resultout = {`Int, accValue < regInValue };
    endcase
end 
endmodule

module tacky_processor(halt, reset, clk);
output halt;
input reset, clk;
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
    #10 clk = 1;
    #10 clk = 0;
  end
  $finish;
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
initial $readmemh("lookup.vmem", look);
//initial $readmemh2(look);
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

// Testing
/*
module testbench;
reg `FLOAT a, b;
reg `WORD r;
wire `FLOAT addr,mulr, recr, shir, i2fr;
wire `INT f2ir, i, j, ia, ib, addri;
reg `WORD ref[1024:0];
f2i myfa(ia, a);
f2i myfb(ib, b);
fadd myadd(addr, a, b);
f2i myaddf(addri, addr);
fmul mymul(mulr, a, b);
frecip myrecip(recr, a);
fshift myshift(shir, a, f2ir);
f2i myf2i(f2ir, a);
f2i myib(i, b);
f2i myiadd(j, addr);
i2f myi2f(i2fr, f2ir);
initial begin
  $readmemh1(ref);
  r = 0;

  while (ref[r] != 0) begin
    a = ref[r]; b = ref[r+1];
    #1 $display("Testing (int)%x = %d, (int)%x = %d", a, ia, b, ib);
    if (addr != ref[r+2]) $display("%x + %x = %x # %x", a, b, addr, ref[r+2]);
    if (mulr != ref[r+3]) $display("%x * %x = %x # %x", a, b, mulr, ref[r+3]);
    if (recr != ref[r+4]) $display("1 / %x = %x # %x", a, recr, ref[r+4]);
    r = r + 5;
  end
end
endmodule
*/

