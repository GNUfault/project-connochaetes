`timescale 1ns / 1ps

module riscv_core_tb;

    reg clk;
    reg reset;
    wire [31:0] pc;
    wire [31:0] instr;
    wire [31:0] mem_addr;
    wire [31:0] mem_wdata;
    wire [3:0]  mem_wstrb;
    wire        mem_valid;
    wire        mem_wen;
    reg         mem_ready;
    reg  [31:0] mem_rdata;

    reg [31:0] imem [0:255];

    reg [31:0] dmem [0:255];

    riscv_core uut (
        .clk(clk),
        .reset(reset),
        .pc(pc),
        .instr(instr),
        .mem_addr(mem_addr),
        .mem_wdata(mem_wdata),
        .mem_wstrb(mem_wstrb),
        .mem_valid(mem_valid),
        .mem_wen(mem_wen),
        .mem_ready(mem_ready),
        .mem_rdata(mem_rdata)
    );

    initial begin
        clk = 0;
        forever #5 clk = ~clk;
    end

    assign instr = imem[pc[31:2]];

    integer j;
    always @(posedge clk) begin
        mem_ready <= 1'b0;
        if (mem_valid && !mem_ready) begin
            if (mem_wen) begin

                if (mem_wstrb[0]) dmem[mem_addr[31:2]][7:0]   <= mem_wdata[7:0];
                if (mem_wstrb[1]) dmem[mem_addr[31:2]][15:8]  <= mem_wdata[15:8];
                if (mem_wstrb[2]) dmem[mem_addr[31:2]][23:16] <= mem_wdata[23:16];
                if (mem_wstrb[3]) dmem[mem_addr[31:2]][31:24] <= mem_wdata[31:24];
                mem_ready <= 1'b1;
            end else begin

                mem_rdata <= dmem[mem_addr[31:2]];
                mem_ready <= 1'b1;
            end
        end
    end

    initial begin

        for (j = 0; j < 256; j = j + 1) begin
            imem[j] = 32'h00000013; // NOP (addi x0, x0, 0)
            dmem[j] = 32'h00000000;
        end

        imem[0] = 32'h00500093;  // addi x1, x0, 5      (x1 = 5)
        imem[1] = 32'h00300113;  // addi x2, x0, 3      (x2 = 3)
        imem[2] = 32'h002081b3;  // add  x3, x1, x2     (x3 = 8)
        imem[3] = 32'h40208233;  // sub  x4, x1, x2     (x4 = 2)

        imem[4] = 32'h00f00293;  // addi x5, x0, 15     (x5 = 15)
        imem[5] = 32'h00c00313;  // addi x6, x0, 12     (x6 = 12)
        imem[6] = 32'h0062f3b3;  // and  x7, x5, x6     (x7 = 12)
        imem[7] = 32'h0062e433;  // or   x8, x5, x6     (x8 = 15)
        imem[8] = 32'h0062c4b3;  // xor  x9, x5, x6     (x9 = 3)

        imem[9]  = 32'h00409513;  // slli x10, x1, 4     (x10 = 5 << 4 = 80)
        imem[10] = 32'h00455593;  // srli x11, x10, 4    (x11 = 80 >> 4 = 5)

        imem[11] = 32'h12345637;  // lui  x12, 0x12345   (x12 = 0x12345000)

        imem[12] = 32'h01400693;  // addi x13, x0, 20    (x13 = 20)
        imem[13] = 32'h00d02023;  // sw   x13, 0(x0)     (mem[0] = 20)
        imem[14] = 32'h00002703;  // lw   x14, 0(x0)     (x14 = mem[0] = 20)

        imem[15] = 32'h0ff00793;  // addi x15, x0, 255   (x15 = 255)
        imem[16] = 32'h00f02223;  // sw   x15, 4(x0)     (mem[4] = 255)
        imem[17] = 32'h00400803;  // lb   x16, 4(x0)     (x16 = sign_ext(255) = -1)
        imem[18] = 32'h00404883;  // lbu  x17, 4(x0)     (x17 = 255)

        imem[19] = 32'h00100913;  // addi x18, x0, 1     (x18 = 1)
        imem[20] = 32'h00100993;  // addi x19, x0, 1     (x19 = 1)
        imem[21] = 32'h01390463;  // beq  x18, x19, +8   (branch taken, skip next 2)
        imem[22] = 32'h00000a13;  // addi x20, x0, 0     (skipped)
        imem[23] = 32'h00000a93;  // addi x21, x0, 0     (skipped)
        imem[24] = 32'h00100b13;  // addi x22, x0, 1     (x22 = 1)

        imem[25] = 32'h008000ef;  // jal  x1, +8         (x1 = PC+4, jump forward 2)
        imem[26] = 32'h00000b93;  // addi x23, x0, 0     (skipped)
        imem[27] = 32'h00200c13;  // addi x24, x0, 2     (x24 = 2)

        imem[28] = 32'h30500073;  // csrrw x0, mtvec, x0 (read mtvec)
        imem[29] = 32'h34102c73;  // csrrs x24, mepc, x0 (read mepc into x24)

        imem[30] = 32'h0000006f;  // jal  x0, 0          (infinite loop)

        reset = 1;
        mem_ready = 0;
        mem_rdata = 0;

        #20;
        reset = 0;

        #5000;

        $display("\n=== Test Results ===");
        $display("x1  = %h (should be address after JAL)", uut.regs[1]);
        $display("x3  = %h (should be 8)", uut.regs[3]);
        $display("x4  = %h (should be 2)", uut.regs[4]);
        $display("x7  = %h (should be c)", uut.regs[7]);
        $display("x8  = %h (should be f)", uut.regs[8]);
        $display("x9  = %h (should be 3)", uut.regs[9]);
        $display("x10 = %h (should be 50)", uut.regs[10]);
        $display("x12 = %h (should be 12345000)", uut.regs[12]);
        $display("x14 = %h (should be 14)", uut.regs[14]);
        $display("x16 = %h (should be ffffffff)", uut.regs[16]);
        $display("x17 = %h (should be ff)", uut.regs[17]);
        $display("x22 = %h (should be 1)", uut.regs[22]);
        $display("x24 = %h (should be 2)", uut.regs[24]);

        $display("\nData Memory:");
        $display("dmem[0] = %h (should be 14)", dmem[0]);
        $display("dmem[1] = %h (should be ff)", dmem[1]);

        $finish;
    end

    initial begin
        $dumpfile("riscv_core_tb.vcd");
        $dumpvars(0, riscv_core_tb);
    end

    initial begin
        $monitor("Time=%0t PC=%h Instr=%h | x1=%h x3=%h x14=%h", 
                 $time, pc, instr, uut.regs[1], uut.regs[3], uut.regs[14]);
    end

endmodule
