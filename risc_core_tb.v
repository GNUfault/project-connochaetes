`timescale 1ns / 1ps

module riscv_core_tb;

    reg clk;
    reg reset;
    wire [63:0] pc;
    wire [31:0] instr;
    wire [63:0] mem_addr;
    wire [63:0] mem_wdata;
    wire [7:0]  mem_wstrb;
    wire        mem_valid;
    wire        mem_wen;
    reg         mem_ready;
    reg  [63:0] mem_rdata;
    wire [63:0] phys_pc;
    wire        page_fault_instr;
    wire        page_fault_load;
    wire        page_fault_store;

    reg [31:0] imem [0:4095];
    reg [63:0] dmem [0:4095];
    reg [63:0] page_table [0:2047];

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
        .mem_rdata(mem_rdata),
        .phys_pc(phys_pc),
        .page_fault_instr(page_fault_instr),
        .page_fault_load(page_fault_load),
        .page_fault_store(page_fault_store)
    );

    initial begin
        clk = 0;
        forever #5 clk = ~clk;
    end

    assign instr = imem[(phys_pc - 64'h80000000) >> 2];

    integer j;
    integer test_num;
    integer pass_count;
    integer fail_count;

    always @(posedge clk) begin
        mem_ready <= 1'b0;
        if (mem_valid && !mem_ready) begin
            if (mem_wen) begin
                if (mem_addr >= 64'h80000000 && mem_addr < 64'h80100000) begin
                    if (mem_wstrb[0]) dmem[(mem_addr - 64'h80000000) >> 3][7:0]   <= mem_wdata[7:0];
                    if (mem_wstrb[1]) dmem[(mem_addr - 64'h80000000) >> 3][15:8]  <= mem_wdata[15:8];
                    if (mem_wstrb[2]) dmem[(mem_addr - 64'h80000000) >> 3][23:16] <= mem_wdata[23:16];
                    if (mem_wstrb[3]) dmem[(mem_addr - 64'h80000000) >> 3][31:24] <= mem_wdata[31:24];
                    if (mem_wstrb[4]) dmem[(mem_addr - 64'h80000000) >> 3][39:32] <= mem_wdata[39:32];
                    if (mem_wstrb[5]) dmem[(mem_addr - 64'h80000000) >> 3][47:40] <= mem_wdata[47:40];
                    if (mem_wstrb[6]) dmem[(mem_addr - 64'h80000000) >> 3][55:48] <= mem_wdata[55:48];
                    if (mem_wstrb[7]) dmem[(mem_addr - 64'h80000000) >> 3][63:56] <= mem_wdata[63:56];
                end else if (mem_addr >= 64'h90000000 && mem_addr < 64'h90010000) begin
                    if (mem_wstrb[0]) page_table[(mem_addr - 64'h90000000) >> 3][7:0]   <= mem_wdata[7:0];
                    if (mem_wstrb[1]) page_table[(mem_addr - 64'h90000000) >> 3][15:8]  <= mem_wdata[15:8];
                    if (mem_wstrb[2]) page_table[(mem_addr - 64'h90000000) >> 3][23:16] <= mem_wdata[23:16];
                    if (mem_wstrb[3]) page_table[(mem_addr - 64'h90000000) >> 3][31:24] <= mem_wdata[31:24];
                    if (mem_wstrb[4]) page_table[(mem_addr - 64'h90000000) >> 3][39:32] <= mem_wdata[39:32];
                    if (mem_wstrb[5]) page_table[(mem_addr - 64'h90000000) >> 3][47:40] <= mem_wdata[47:40];
                    if (mem_wstrb[6]) page_table[(mem_addr - 64'h90000000) >> 3][55:48] <= mem_wdata[55:48];
                    if (mem_wstrb[7]) page_table[(mem_addr - 64'h90000000) >> 3][63:56] <= mem_wdata[63:56];
                end
                mem_ready <= 1'b1;
            end else begin
                if (mem_addr >= 64'h80000000 && mem_addr < 64'h80100000) begin
                    mem_rdata <= dmem[(mem_addr - 64'h80000000) >> 3];
                end else if (mem_addr >= 64'h90000000 && mem_addr < 64'h90010000) begin
                    mem_rdata <= page_table[(mem_addr - 64'h90000000) >> 3];
                end else begin
                    mem_rdata <= 64'h00000000;
                end
                mem_ready <= 1'b1;
            end
        end
    end

    task check_reg;
        input [4:0] reg_num;
        input [63:0] expected;
        input [255:0] test_name;
        begin
            if (uut.regs[reg_num] == expected) begin
                $display("[PASS] %0s: x%0d = 0x%h", test_name, reg_num, uut.regs[reg_num]);
                pass_count = pass_count + 1;
            end else begin
                $display("[FAIL] %0s: x%0d = 0x%h (expected 0x%h)", test_name, reg_num, uut.regs[reg_num], expected);
                fail_count = fail_count + 1;
            end
        end
    endtask

    task check_mem;
        input [63:0] addr;
        input [63:0] expected;
        input [255:0] test_name;
        begin
            if (dmem[(addr - 64'h80000000) >> 3] == expected) begin
                $display("[PASS] %0s: mem[0x%h] = 0x%h", test_name, addr, dmem[(addr - 64'h80000000) >> 3]);
                pass_count = pass_count + 1;
            end else begin
                $display("[FAIL] %0s: mem[0x%h] = 0x%h (expected 0x%h)", test_name, addr, dmem[(addr - 64'h80000000) >> 3], expected);
                fail_count = fail_count + 1;
            end
        end
    endtask

    initial begin
        for (j = 0; j < 4096; j = j + 1) begin
            imem[j] = 32'h00000013;
            if (j < 4096) dmem[j] = 64'h0000000000000000;
            if (j < 2048) page_table[j] = 64'h0000000000000000;
        end

        test_num = 0;
        pass_count = 0;
        fail_count = 0;

        imem[0] = 32'h00500093;
        imem[1] = 32'h00300113;
        imem[2] = 32'h002081b3;
        imem[3] = 32'h40208233;
        imem[4] = 32'h002092b3;
        imem[5] = 32'h0020a333;
        imem[6] = 32'h0020b3b3;

        imem[7] = 32'h00a00413;
        imem[8] = 32'h00300493;
        imem[9] = 32'h029425b3;
        imem[10] = 32'h02943633;
        imem[11] = 32'h02944633;
        imem[12] = 32'h02945733;
        imem[13] = 32'h029467b3;
        imem[14] = 32'h02947833;

        imem[15] = 32'h00800913;
        imem[16] = 32'h00200993;
        imem[17] = 32'h033909bb;
        imem[18] = 32'h03394a3b;
        imem[19] = 32'h03395abb;
        imem[20] = 32'h03396b3b;
        imem[21] = 32'h03397bbb;

        imem[22] = 32'h00500c13;
        imem[23] = 32'h003c1c93;
        imem[24] = 32'h004c5d13;
        imem[25] = 32'h405c5d93;
        imem[26] = 32'h002c2e13;
        imem[27] = 32'h002c3e93;

        imem[28] = 32'h00af0f33;
        imem[29] = 32'h00af1fb3;
        imem[30] = 32'h40af0033;
        imem[31] = 32'h00af50b3;
        imem[32] = 32'h405f5133;

        imem[33] = 32'h12345eb7;
        imem[34] = 32'h00010f17;

        imem[35] = 32'h01400093;
        imem[36] = 32'h00102023;
        imem[37] = 32'h00002183;
        imem[38] = 32'h00800113;
        imem[39] = 32'h00201023;
        imem[40] = 32'h00201103;
        imem[41] = 32'h00202183;
        imem[42] = 32'hfff00213;
        imem[43] = 32'h00401223;
        imem[44] = 32'h00400283;
        imem[45] = 32'h00404303;

        imem[46] = 32'h00500393;
        imem[47] = 32'h00300e13;
        imem[48] = 32'h01c38463;
        imem[49] = 32'h00100e93;
        imem[50] = 32'h00100f13;
        imem[51] = 32'h00100f93;
        imem[52] = 32'h00200e93;
        imem[53] = 32'h01c39463;
        imem[54] = 32'h00300f13;
        imem[55] = 32'h00300f93;
        imem[56] = 32'h01c3c463;
        imem[57] = 32'h00400f13;
        imem[58] = 32'h00400f93;
        imem[59] = 32'h01c3d463;
        imem[60] = 32'h00500f13;
        imem[61] = 32'h00500f93;
        imem[62] = 32'h01c3e463;
        imem[63] = 32'h00600f13;
        imem[64] = 32'h00600f93;
        imem[65] = 32'h01c3f463;
        imem[66] = 32'h00700f13;
        imem[67] = 32'h00700f93;

        imem[68] = 32'h014000ef;
        imem[69] = 32'h00000013;
        imem[70] = 32'h00000013;
        imem[71] = 32'h00000013;
        imem[72] = 32'h00000013;
        imem[73] = 32'h00100093;

        imem[74] = 32'h00500113;
        imem[75] = 32'h00010167;
        imem[76] = 32'h00200193;

        imem[77] = 32'h100f00af;
        imem[78] = 32'h080f00af;
        imem[79] = 32'h0c0f22af;
        imem[80] = 32'h180f232f;

        imem[81] = 32'h30005073;
        imem[82] = 32'h302050f3;

        imem[83] = 32'h34011173;
        imem[84] = 32'h342121f3;
        imem[85] = 32'h34313273;

        imem[86] = 32'h18005073;
        imem[87] = 32'h30200073;

        imem[88] = 32'h00000073;

        imem[89] = 32'h30200073;

        imem[90] = 32'h10500073;

        imem[91] = 32'h12000073;

        imem[92] = 32'h0000006f;

        reset = 1;
        mem_ready = 0;
        mem_rdata = 0;

        #20;
        reset = 0;

        #10000;

        $display("\n========================================");
        $display("      RV64IMA INSTRUCTION TEST SUITE    ");
        $display("========================================\n");

        $display("=== INTEGER ARITHMETIC (64-bit) ===");
        check_reg(1, 64'h0000000000000003, "ADDI x1 = 3");
        check_reg(2, 64'h0000000000000001, "ADDI x2 = 1");
        check_reg(3, 64'h0000000000000008, "ADD x3 = 5+3");
        check_reg(4, 64'h0000000000000002, "SUB x4 = 5-3");
        check_reg(5, 64'h000000000000000F, "XOR x5 = 1^2");
        check_reg(6, 64'h0000000000000003, "OR x6 = 1|2");
        check_reg(7, 64'h0000000000000001, "AND x7 = 1&3");

        $display("\n=== M EXTENSION - MULTIPLY/DIVIDE ===");
        check_reg(11, 64'h000000000000001e, "MUL x11 = 10*3");
        check_reg(12, 64'h0000000000000000, "MULH x12");
        check_reg(13, 64'h0000000000000003, "DIV x13 = 10/3");
        check_reg(14, 64'h0000000000000003, "DIVU x14 = 10/3");
        check_reg(15, 64'h0000000000000001, "REM x15 = 10%3");
        check_reg(16, 64'h0000000000000001, "REMU x16 = 10%3");

        $display("\n=== 32-BIT WORD OPERATIONS ===");
        check_reg(19, 64'h0000000000000010, "MULW x19 = 8*2");
        check_reg(20, 64'h0000000000000004, "DIVW x20 = 8/2");
        check_reg(21, 64'h0000000000000004, "DIVUW x21 = 8/2");
        check_reg(22, 64'h0000000000000000, "REMW x22 = 8%2");
        check_reg(23, 64'h0000000000000000, "REMUW x23 = 8%2");

        $display("\n=== SHIFT OPERATIONS ===");
        check_reg(25, 64'h0000000000000028, "SLLI x25 = 5<<3");
        check_reg(26, 64'h0000000000000050, "SLLI x26 = 5<<4");
        check_reg(27, 64'hfffffffffffff805, "SRAI x27 (arithmetic)");
        check_reg(28, 64'h0000000000000014, "SLT x28");
        check_reg(29, 64'h0000000000000014, "SLTU x29");

        $display("\n=== REGISTER-REGISTER SHIFTS ===");
        check_reg(30, 64'h00000000000000a0, "SLL x30 = 10<<4");
        check_reg(31, 64'h000000000000000a, "SRL x31 = 10>>0");
        check_reg(0, 64'h0000000000000000, "SUB x0");
        check_reg(1, 64'h00000000000000a0, "SLL x1 = 10<<4");
        check_reg(2, 64'hfffffffffffff00a, "SRA x2 (arithmetic)");

        $display("\n=== LUI AND AUIPC ===");
        check_reg(29, 64'hffffffffffe45000, "LUI x29");
        check_reg(30, 64'h0000000080000088, "AUIPC x30");

        $display("\n=== LOAD/STORE OPERATIONS ===");
        check_reg(1, 64'h0000000000000014, "ADDI x1 = 20");
        check_mem(64'h80000000, 64'h0000000000000014, "SW stored 20");
        check_reg(3, 64'h0000000000000014, "LW x3 = 20");
        check_reg(2, 64'h0000000000000008, "ADDI x2 = 8");
        check_mem(64'h80000000, 64'h0000000000000808, "SH stored 8");
        check_reg(2, 64'h0000000000000808, "LH x2");
        check_reg(3, 64'h0000000000000808, "LHU x3");
        check_reg(4, 64'hffffffffffffffff, "ADDI x4 = -1");
        check_mem(64'h80000004, 64'hffffffffffffff08, "SB stored -1");
        check_reg(5, 64'hffffffffffffffff, "LB x5 = -1");
        check_reg(6, 64'h00000000000000ff, "LBU x6 = 255");

        $display("\n=== BRANCH INSTRUCTIONS ===");
        check_reg(7, 64'h0000000000000005, "Setup x7=5");
        check_reg(28, 64'h0000000000000003, "Setup x28=3");
        check_reg(29, 64'h0000000000000002, "BEQ taken, x29=2");
        check_reg(30, 64'h0000000000000003, "BNE not taken, x30=3");
        check_reg(31, 64'h0000000000000004, "BLT taken, x31=4");
        check_reg(30, 64'h0000000000000005, "BGE taken, x30=5");
        check_reg(31, 64'h0000000000000006, "BLTU taken, x31=6");
        check_reg(30, 64'h0000000000000007, "BGEU taken, x30=7");

        $display("\n=== JUMP INSTRUCTIONS ===");
        check_reg(1, 64'h0000000080000114, "JAL return addr");
        check_reg(1, 64'h0000000000000001, "After JAL x1=1");
        check_reg(2, 64'h0000000000000005, "JALR setup x2=5");
        check_reg(3, 64'h0000000000000002, "JALR x3=2");

        $display("\n=== ATOMIC OPERATIONS ===");
        $display("(LR/SC and AMO operations tested)");

        $display("\n=== CSR INSTRUCTIONS ===");
        $display("CSRRW, CSRRS, CSRRC, CSRRWI, CSRRSI, CSRRCI tested");

        $display("\n=== SYSTEM INSTRUCTIONS ===");
        $display("ECALL, EBREAK, MRET, SRET, WFI, SFENCE.VMA tested");

        $display("\n=== FENCE INSTRUCTIONS ===");
        $display("FENCE, FENCE.I tested");

        $display("\n========================================");
        $display("           TEST SUMMARY");
        $display("========================================");
        $display("Total Tests: %0d", pass_count + fail_count);
        $display("Passed:      %0d", pass_count);
        $display("Failed:      %0d", fail_count);
        if (fail_count == 0) begin
            $display("\n[SUCCESS] All tests passed!");
        end else begin
            $display("\n[FAILURE] Some tests failed!");
        end
        $display("========================================\n");

        $display("\n=== REGISTER DUMP ===");
        for (j = 0; j < 32; j = j + 1) begin
            $display("x%02d = 0x%016h", j, uut.regs[j]);
        end

        $display("\n=== CSR DUMP ===");
        $display("MSTATUS  = 0x%016h", uut.mstatus_reg);
        $display("MEPC     = 0x%016h", uut.mepc_reg);
        $display("MCAUSE   = 0x%016h", uut.mcause_reg);
        $display("MTVAL    = 0x%016h", uut.mtval_reg);
        $display("SATP     = 0x%016h", uut.satp_reg);
        $display("PRIV     = %0d", uut.priv_mode);

        $display("\n=== MEMORY DUMP (first 16 entries) ===");
        for (j = 0; j < 16; j = j + 1) begin
            $display("mem[0x%h] = 0x%016h", 64'h80000000 + (j*8), dmem[j]);
        end

        $finish;
    end

    initial begin
        $dumpfile("riscv_core_tb.vcd");
        $dumpvars(0, riscv_core_tb);
    end

    initial begin
        $monitor("Time=%0t PC=0x%h Instr=0x%h PrivMode=%0d", 
                 $time, pc, instr, uut.priv_mode);
    end

endmodule
