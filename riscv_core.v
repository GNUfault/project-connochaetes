`timescale 1ns / 1ps

module riscv_core (
    input  wire        clk,
    input  wire        reset,
    output reg  [31:0] pc,
    input  wire [31:0] instr,
    output reg  [31:0] mem_addr,
    output reg  [31:0] mem_wdata,
    output reg  [3:0]  mem_wstrb,
    output reg         mem_valid,
    output reg         mem_wen,
    input  wire        mem_ready,
    input  wire [31:0] mem_rdata
);

    reg [31:0] regs [0:31];
    integer i;

    reg [31:0] mstatus_reg;
    reg [31:0] mepc_reg;
    reg [31:0] mcause_reg;
    reg [31:0] mtvec_reg;

    localparam CSR_MSTATUS = 12'h300;
    localparam CSR_MEPC    = 12'h341;
    localparam CSR_MCAUSE  = 12'h342;
    localparam CSR_MTVEC   = 12'h305;

    wire [6:0] opcode = instr[6:0];
    wire [4:0] rd     = instr[11:7];
    wire [2:0] funct3 = instr[14:12];
    wire [4:0] rs1    = instr[19:15];
    wire [4:0] rs2    = instr[24:20];
    wire [6:0] funct7 = instr[31:25];
    wire [11:0] csr_addr = instr[31:20];

    wire [31:0] src1 = (rs1 == 0) ? 32'b0 : regs[rs1];
    wire [31:0] src2_reg = (rs2 == 0) ? 32'b0 : regs[rs2];

    wire [31:0] imm_i = {{20{instr[31]}}, instr[31:20]};
    wire [31:0] imm_s = {{20{instr[31]}}, instr[31:25], instr[11:7]};
    wire [31:0] imm_b = {{19{instr[31]}}, instr[31], instr[7], instr[30:25], instr[11:8], 1'b0};
    wire [31:0] imm_u = {instr[31:12], 12'b0};
    wire [31:0] imm_j = {{11{instr[31]}}, instr[31], instr[19:12], instr[20], instr[30:21], 1'b0};

    wire is_op_imm = (opcode == 7'b0010011);
    wire is_op     = (opcode == 7'b0110011);
    wire is_lui    = (opcode == 7'b0110111);
    wire is_auipc  = (opcode == 7'b0010111);
    wire is_load   = (opcode == 7'b0000011);
    wire is_store  = (opcode == 7'b0100011);
    wire is_branch = (opcode == 7'b1100011);
    wire is_jal    = (opcode == 7'b1101111);
    wire is_jalr   = (opcode == 7'b1100111);
    wire is_system = (opcode == 7'b1110011);

    wire [31:0] src2_alu = is_op ? src2_reg : imm_i;

    reg [31:0] alu_result;
    always @(*) begin
        if (is_lui) begin
            alu_result = imm_u;
        end else if (is_auipc) begin
            alu_result = pc + imm_u;
        end else if (is_jal || is_jalr) begin
            alu_result = pc + 32'd4;
        end else begin
            case (funct3)
                3'b000: alu_result = (is_op && funct7[5]) ? (src1 - src2_reg) : (src1 + src2_alu);
                3'b100: alu_result = src1 ^ src2_alu;
                3'b110: alu_result = src1 | src2_alu;
                3'b111: alu_result = src1 & src2_alu;
                3'b001: alu_result = src1 << src2_alu[4:0];
                3'b101: alu_result = (is_op ? (funct7[5] ? ($signed(src1) >>> src2_reg[4:0]) : (src1 >> src2_reg[4:0]))
                                            : (funct7[5] ? ($signed(src1) >>> src2_alu[4:0]) : (src1 >> src2_alu[4:0])));
                3'b010: alu_result = ($signed(src1) < $signed(src2_alu)) ? 32'd1 : 32'd0;
                3'b011: alu_result = (src1 < src2_alu) ? 32'd1 : 32'd0;
                default: alu_result = 32'b0;
            endcase
        end
    end

    wire beq  = is_branch && (funct3 == 3'b000);
    wire bne  = is_branch && (funct3 == 3'b001);
    wire blt  = is_branch && (funct3 == 3'b100);
    wire bge  = is_branch && (funct3 == 3'b101);
    wire bltu = is_branch && (funct3 == 3'b110);
    wire bgeu = is_branch && (funct3 == 3'b111);

    wire branch_taken =
        (beq  && (src1 == src2_reg)) ||
        (bne  && (src1 != src2_reg)) ||
        (blt  && ($signed(src1) <  $signed(src2_reg))) ||
        (bge  && ($signed(src1) >= $signed(src2_reg))) ||
        (bltu && (src1 <  src2_reg)) ||
        (bgeu && (src1 >= src2_reg));

    wire is_csr = is_system && (funct3 != 3'b000);
    wire is_ecall = is_system && (funct3 == 3'b000) && (instr[31:20] == 12'h000);
    wire is_mret  = is_system && (funct3 == 3'b000) && (instr[31:20] == 12'h302);

    reg [31:0] csr_old;
    always @(*) begin
        case (csr_addr)
            CSR_MSTATUS: csr_old = mstatus_reg;
            CSR_MEPC:    csr_old = mepc_reg;
            CSR_MCAUSE:  csr_old = mcause_reg;
            CSR_MTVEC:   csr_old = mtvec_reg;
            default:     csr_old = 32'b0;
        endcase
    end

    wire [4:0] zimm = rs1;
    reg [31:0] csr_new;
    always @(*) begin
        csr_new = csr_old;
        case (funct3)
            3'b001: csr_new = src1;
            3'b010: csr_new = csr_old | src1;
            3'b011: csr_new = csr_old & ~src1;
            3'b101: csr_new = {27'b0, zimm};
            3'b110: csr_new = csr_old | {27'b0, zimm};
            3'b111: csr_new = csr_old & ~{27'b0, zimm};
            default: csr_new = csr_old;
        endcase
    end

    wire is_shift_imm = is_op_imm && ((funct3 == 3'b001) || (funct3 == 3'b101));
    wire shamt_hi = instr[25];
    wire illegal_shift_imm = is_shift_imm && shamt_hi;

    wire csr_addr_valid = (csr_addr == CSR_MSTATUS) | (csr_addr == CSR_MEPC) | (csr_addr == CSR_MCAUSE) | (csr_addr == CSR_MTVEC);

    wire illegal_op_base =
        ~(is_op_imm | is_op | is_lui | is_auipc | is_load | is_store | is_branch | is_jal | is_jalr | is_system);

    wire illegal_op = illegal_op_base | (is_csr && ~csr_addr_valid) | illegal_shift_imm;

    wire [31:0] eff_addr = src1 + (is_store ? imm_s : imm_i);

    wire misalign_lh = is_load && (funct3 == 3'b001 || funct3 == 3'b101) && eff_addr[0];
    wire misalign_lw = is_load && (funct3 == 3'b010) && (eff_addr[1:0] != 2'b00);
    wire misalign_sh = is_store && (funct3 == 3'b001) && eff_addr[0];
    wire misalign_sw = is_store && (funct3 == 3'b010) && (eff_addr[1:0] != 2'b00);
    wire misalign = misalign_lh | misalign_lw | misalign_sh | misalign_sw;

    wire [31:0] misalign_cause = is_load ? 32'd4 : 32'd6;

    wire take_trap = is_ecall | illegal_op | misalign;
    wire [31:0] trap_cause = is_ecall ? 32'd11 : (misalign ? misalign_cause : 32'd2);

    wire [1:0] addr_byte = eff_addr[1:0];
    wire [7:0] byte_sel  = (addr_byte == 2'b00) ? mem_rdata[7:0]   :
                           (addr_byte == 2'b01) ? mem_rdata[15:8]  :
                           (addr_byte == 2'b10) ? mem_rdata[23:16] :
                                                  mem_rdata[31:24];
    wire [15:0] half_sel = (eff_addr[1] == 1'b0) ? mem_rdata[15:0] : mem_rdata[31:16];

    reg [31:0] load_data;
    always @(*) begin
        case (funct3)
            3'b000: load_data = {{24{byte_sel[7]}}, byte_sel};
            3'b100: load_data = {24'b0, byte_sel};
            3'b001: load_data = {{16{half_sel[15]}}, half_sel};
            3'b101: load_data = {16'b0, half_sel};
            3'b010: load_data = mem_rdata;
            default: load_data = 32'b0;
        endcase
    end

    reg [3:0] wstrb_comb;
    always @(*) begin
        wstrb_comb = 4'b0000;
        if (is_store) begin
            case (funct3)
                3'b000: wstrb_comb = 4'b0001 << addr_byte;
                3'b001: wstrb_comb = eff_addr[1] ? 4'b1100 : 4'b0011;
                3'b010: wstrb_comb = 4'b1111;
                default: wstrb_comb = 4'b0000;
            endcase
        end
    end

    reg mem_req_pending;
    reg is_load_pending;
    reg [4:0] rd_pending;

    always @(posedge clk or posedge reset) begin
        if (reset) begin
            pc <= 32'h8000_0000;
            mem_wen <= 1'b0;
            mem_valid <= 1'b0;
            mem_addr <= 32'b0;
            mem_wdata <= 32'b0;
            mem_wstrb <= 4'b0000;
            mstatus_reg <= 32'b0;
            mepc_reg    <= 32'b0;
            mcause_reg  <= 32'b0;
            mtvec_reg   <= 32'b0;
            mem_req_pending <= 1'b0;
            is_load_pending <= 1'b0;
            rd_pending <= 5'b0;
            for (i=0; i<32; i=i+1) regs[i] <= 32'b0;
        end else begin
            mem_wen <= 1'b0;
            mem_valid <= 1'b0;
            mem_wstrb <= 4'b0000;

            if (take_trap) begin
                mepc_reg <= pc;
                mcause_reg <= trap_cause;
                mstatus_reg[7] <= mstatus_reg[3];
                mstatus_reg[3] <= 1'b0;
                pc <= mtvec_reg & ~32'b1;
                mem_req_pending <= 1'b0;
                is_load_pending <= 1'b0;
            end else if (is_mret) begin
                mstatus_reg[3] <= mstatus_reg[7];
                mstatus_reg[7] <= 1'b1;
                pc <= mepc_reg;
            end else if (mem_req_pending) begin
                if (mem_ready) begin
                    if (is_load_pending && rd_pending != 0) regs[rd_pending] <= load_data;
                    mem_req_pending <= 1'b0;
                    is_load_pending <= 1'b0;
                    pc <= pc + 32'd4;
                end
            end else if (is_jal) begin
                if (rd != 0) regs[rd] <= pc + 32'd4;
                pc <= pc + imm_j;
            end else if (is_jalr) begin
                if (rd != 0) regs[rd] <= pc + 32'd4;
                pc <= (src1 + imm_i) & ~32'd1;
            end else if (is_branch) begin
                pc <= branch_taken ? (pc + imm_b) : (pc + 32'd4);
            end else begin
                if (is_lui || is_auipc || is_op_imm || is_op) begin
                    if (rd != 0) regs[rd] <= alu_result;
                end
                if (is_csr) begin
                    if (rd != 0) regs[rd] <= csr_old;
                    if (csr_addr == CSR_MSTATUS) begin
                        mstatus_reg <= csr_new;
                    end else if (csr_addr == CSR_MEPC) begin
                        mepc_reg <= csr_new;
                    end else if (csr_addr == CSR_MCAUSE) begin
                        mcause_reg <= csr_new;
                    end else if (csr_addr == CSR_MTVEC) begin
                        mtvec_reg <= {csr_new[31:2], 2'b00};
                    end
                end
                if (is_load || is_store) begin
                    if (misalign) begin
                        mepc_reg <= pc;
                        mcause_reg <= misalign_cause;
                        mstatus_reg[7] <= mstatus_reg[3];
                        mstatus_reg[3] <= 1'b0;
                        pc <= mtvec_reg & ~32'b1;
                    end else begin
                        mem_addr <= eff_addr;
                        if (is_store) begin
                            mem_wdata <= src2_reg;
                            mem_wstrb <= wstrb_comb;
                            mem_wen <= 1'b1;
                            mem_valid <= 1'b1;
                            mem_req_pending <= 1'b1;
                            is_load_pending <= 1'b0;
                            rd_pending <= 5'b0;
                        end else begin
                            mem_wen <= 1'b0;
                            mem_wstrb <= 4'b0000;
                            mem_valid <= 1'b1;
                            mem_req_pending <= 1'b1;
                            is_load_pending <= 1'b1;
                            rd_pending <= rd;
                        end
                    end
                end else begin
                    pc <= pc + 32'd4;
                end
            end
            regs[0] <= 32'b0;
        end
    end

endmodule
