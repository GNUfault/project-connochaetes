`timescale 1ns / 1ps

module riscv_core (
    input  wire        clk,
    input  wire        reset,
    output reg  [63:0] pc,
    input  wire [31:0] instr,
    output reg  [63:0] mem_addr,
    output reg  [63:0] mem_wdata,
    output reg  [7:0]  mem_wstrb,
    output reg         mem_valid,
    output reg         mem_wen,
    input  wire        mem_ready,
    input  wire [63:0] mem_rdata,
    output wire [63:0] phys_pc,
    output wire        page_fault_instr,
    output wire        page_fault_load,
    output wire        page_fault_store
);

    reg [63:0] regs [0:31];
    integer i;

    reg [63:0] mstatus_reg;
    reg [63:0] medeleg_reg;
    reg [63:0] mideleg_reg;
    reg [63:0] mie_reg;
    reg [63:0] mtvec_reg;
    reg [63:0] mscratch_reg;
    reg [63:0] mepc_reg;
    reg [63:0] mcause_reg;
    reg [63:0] mtval_reg;
    reg [63:0] mip_reg;
    reg [63:0] mcounteren_reg;
    reg [63:0] mcycle_reg;
    reg [63:0] minstret_reg;
    reg [63:0] mhartid_reg;
    reg [63:0] mvendorid_reg;
    reg [63:0] marchid_reg;
    reg [63:0] mimpid_reg;

    reg [63:0] sstatus_reg;
    reg [63:0] sie_reg;
    reg [63:0] stvec_reg;
    reg [63:0] sscratch_reg;
    reg [63:0] sepc_reg;
    reg [63:0] scause_reg;
    reg [63:0] stval_reg;
    reg [63:0] sip_reg;
    reg [63:0] satp_reg;

    localparam CSR_MSTATUS    = 12'h300;
    localparam CSR_MISA       = 12'h301;
    localparam CSR_MEDELEG    = 12'h302;
    localparam CSR_MIDELEG    = 12'h303;
    localparam CSR_MIE        = 12'h304;
    localparam CSR_MTVEC      = 12'h305;
    localparam CSR_MCOUNTEREN = 12'h306;
    localparam CSR_MSCRATCH   = 12'h340;
    localparam CSR_MEPC       = 12'h341;
    localparam CSR_MCAUSE     = 12'h342;
    localparam CSR_MTVAL      = 12'h343;
    localparam CSR_MIP        = 12'h344;
    localparam CSR_MCYCLE     = 12'hB00;
    localparam CSR_MINSTRET   = 12'hB02;
    localparam CSR_MHARTID    = 12'hF14;
    localparam CSR_MVENDORID  = 12'hF11;
    localparam CSR_MARCHID    = 12'hF12;
    localparam CSR_MIMPID     = 12'hF13;

    localparam CSR_SSTATUS    = 12'h100;
    localparam CSR_SIE        = 12'h104;
    localparam CSR_STVEC      = 12'h105;
    localparam CSR_SSCRATCH   = 12'h140;
    localparam CSR_SEPC       = 12'h141;
    localparam CSR_SCAUSE     = 12'h142;
    localparam CSR_STVAL      = 12'h143;
    localparam CSR_SIP        = 12'h144;
    localparam CSR_SATP       = 12'h180;

    localparam CSR_CYCLE      = 12'hC00;
    localparam CSR_TIME       = 12'hC01;
    localparam CSR_INSTRET    = 12'hC02;

    localparam PRIV_U = 2'b00;
    localparam PRIV_S = 2'b01;
    localparam PRIV_M = 2'b11;

    reg [1:0] priv_mode;

    wire [6:0] opcode = instr[6:0];
    wire [4:0] rd     = instr[11:7];
    wire [2:0] funct3 = instr[14:12];
    wire [4:0] rs1    = instr[19:15];
    wire [4:0] rs2    = instr[24:20];
    wire [6:0] funct7 = instr[31:25];
    wire [11:0] csr_addr = instr[31:20];
    wire [4:0] shamt = instr[24:20];
    wire [5:0] shamt6 = instr[25:20];

    wire [63:0] src1 = (rs1 == 0) ? 64'b0 : regs[rs1];
    wire [63:0] src2_reg = (rs2 == 0) ? 64'b0 : regs[rs2];
    wire [31:0] src1_w = src1[31:0];
    wire [31:0] src2_w = src2_reg[31:0];

    wire [63:0] imm_i = {{52{instr[31]}}, instr[31:20]};
    wire [63:0] imm_s = {{52{instr[31]}}, instr[31:25], instr[11:7]};
    wire [63:0] imm_b = {{51{instr[31]}}, instr[31], instr[7], instr[30:25], instr[11:8], 1'b0};
    wire [63:0] imm_u = {{32{instr[31]}}, instr[31:12], 12'b0};
    wire [63:0] imm_j = {{43{instr[31]}}, instr[31], instr[19:12], instr[20], instr[30:21], 1'b0};

    wire is_op_imm   = (opcode == 7'b0010011);
    wire is_op_imm32 = (opcode == 7'b0011011);
    wire is_op       = (opcode == 7'b0110011);
    wire is_op32     = (opcode == 7'b0111011);
    wire is_lui      = (opcode == 7'b0110111);
    wire is_auipc    = (opcode == 7'b0010111);
    wire is_load     = (opcode == 7'b0000011);
    wire is_store    = (opcode == 7'b0100011);
    wire is_branch   = (opcode == 7'b1100011);
    wire is_jal      = (opcode == 7'b1101111);
    wire is_jalr     = (opcode == 7'b1100111);
    wire is_system   = (opcode == 7'b1110011);
    wire is_amo      = (opcode == 7'b0101111);
    wire is_fence    = (opcode == 7'b0001111);

    wire is_word_op = is_op32 | is_op_imm32;

    wire [63:0] src2_alu = (is_op | is_op32) ? src2_reg : imm_i;

    wire is_mul = (is_op || is_op32) && (funct7 == 7'b0000001);
    
    reg [63:0] mul_result;
    reg [63:0] mulh_result;
    wire [127:0] mul_signed = $signed(src1) * $signed(src2_reg);
    wire [127:0] mul_unsigned = src1 * src2_reg;
    wire [127:0] mul_su = $signed(src1) * $unsigned(src2_reg);
    wire [63:0] mul_signed_w = {{32{(src1_w * src2_w)[31]}}, src1_w * src2_w};

    always @(*) begin
        if (is_word_op) begin
            case(funct3)
                3'b000: mul_result = mul_signed_w;
                3'b100: mul_result = (src2_reg == 0) ? 64'hFFFFFFFFFFFFFFFF : {{32{($signed(src1_w) / $signed(src2_w))[31]}}, $signed(src1_w) / $signed(src2_w)};
                3'b101: mul_result = (src2_reg == 0) ? 64'hFFFFFFFFFFFFFFFF : {{32{(src1_w / src2_w)[31]}}, src1_w / src2_w};
                3'b110: mul_result = (src2_reg == 0) ? {{32{src1_w[31]}}, src1_w} : {{32{($signed(src1_w) % $signed(src2_w))[31]}}, $signed(src1_w) % $signed(src2_w)};
                3'b111: mul_result = (src2_reg == 0) ? {{32{src1_w[31]}}, src1_w} : {{32{(src1_w % src2_w)[31]}}, src1_w % src2_w};
                default: mul_result = 64'b0;
            endcase
            mulh_result = 64'b0;
        end else begin
            case(funct3)
                3'b000: begin
                    mul_result = mul_signed[63:0];
                    mulh_result = mul_signed[127:64];
                end
                3'b001: begin
                    mul_result = mul_signed[63:0];
                    mulh_result = mul_signed[127:64];
                end
                3'b010: begin
                    mul_result = mul_signed[63:0];
                    mulh_result = mul_su[127:64];
                end
                3'b011: begin
                    mul_result = mul_unsigned[63:0];
                    mulh_result = mul_unsigned[127:64];
                end
                3'b100: begin
                    mul_result = (src2_reg == 0) ? 64'hFFFFFFFFFFFFFFFF : ($signed(src1) / $signed(src2_reg));
                    mulh_result = 64'b0;
                end
                3'b101: begin
                    mul_result = (src2_reg == 0) ? 64'hFFFFFFFFFFFFFFFF : (src1 / src2_reg);
                    mulh_result = 64'b0;
                end
                3'b110: begin
                    mul_result = (src2_reg == 0) ? src1 : ($signed(src1) % $signed(src2_reg));
                    mulh_result = 64'b0;
                end
                3'b111: begin
                    mul_result = (src2_reg == 0) ? src1 : (src1 % src2_reg);
                    mulh_result = 64'b0;
                end
            endcase
        end
    end

    reg [63:0] alu_result;
    always @(*) begin
        if (is_lui) begin
            alu_result = imm_u;
        end else if (is_auipc) begin
            alu_result = pc + imm_u;
        end else if (is_jal || is_jalr) begin
            alu_result = pc + 64'd4;
        end else if (is_mul) begin
            if (funct3 == 3'b001)
                alu_result = mulh_result;
            else
                alu_result = mul_result;
        end else if (is_word_op) begin
            case (funct3)
                3'b000: alu_result = {{32{(((is_op32 && funct7[5]) ? (src1_w - src2_w) : (src1_w + src2_alu[31:0])))[31]}}, (is_op32 && funct7[5]) ? (src1_w - src2_w) : (src1_w + src2_alu[31:0])};
                3'b001: alu_result = {{32{(src1_w << src2_alu[4:0])[31]}}, src1_w << src2_alu[4:0]};
                3'b101: alu_result = (is_op32 ? (funct7[5] ? {{32{($signed(src1_w) >>> src2_w[4:0])[31]}}, $signed(src1_w) >>> src2_w[4:0]} : {{32{(src1_w >> src2_w[4:0])[31]}}, src1_w >> src2_w[4:0]})
                                             : (funct7[5] ? {{32{($signed(src1_w) >>> src2_alu[4:0])[31]}}, $signed(src1_w) >>> src2_alu[4:0]} : {{32{(src1_w >> src2_alu[4:0])[31]}}, src1_w >> src2_alu[4:0]}));
                default: alu_result = 64'b0;
            endcase
        end else begin
            case (funct3)
                3'b000: alu_result = (is_op && funct7[5]) ? (src1 - src2_reg) : (src1 + src2_alu);
                3'b100: alu_result = src1 ^ src2_alu;
                3'b110: alu_result = src1 | src2_alu;
                3'b111: alu_result = src1 & src2_alu;
                3'b001: alu_result = src1 << (is_op ? src2_reg[5:0] : shamt6);
                3'b101: alu_result = (is_op ? (funct7[5] ? ($signed(src1) >>> src2_reg[5:0]) : (src1 >> src2_reg[5:0]))
                                            : (funct7[5] ? ($signed(src1) >>> shamt6) : (src1 >> shamt6)));
                3'b010: alu_result = ($signed(src1) < $signed(src2_alu)) ? 64'd1 : 64'd0;
                3'b011: alu_result = (src1 < src2_alu) ? 64'd1 : 64'd0;
                default: alu_result = 64'b0;
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
    wire is_ebreak = is_system && (funct3 == 3'b000) && (instr[31:20] == 12'h001);
    wire is_mret  = is_system && (funct3 == 3'b000) && (instr[31:20] == 12'h302);
    wire is_sret  = is_system && (funct3 == 3'b000) && (instr[31:20] == 12'h102);
    wire is_wfi   = is_system && (funct3 == 3'b000) && (instr[31:20] == 12'h105);
    wire is_sfence_vma = is_system && (funct3 == 3'b000) && (funct7 == 7'b0001001);

    wire [63:0] misa_value = 64'h8000000000141129;

    wire mstatus_tsr = mstatus_reg[22];
    wire mstatus_tw  = mstatus_reg[21];
    wire mstatus_tvm = mstatus_reg[20];
    wire mstatus_mxr = mstatus_reg[19];
    wire mstatus_sum = mstatus_reg[18];
    wire mstatus_mprv = mstatus_reg[17];
    wire [1:0] mstatus_mpp = mstatus_reg[12:11];
    wire mstatus_spp = mstatus_reg[8];
    wire mstatus_mpie = mstatus_reg[7];
    wire mstatus_spie = mstatus_reg[5];
    wire mstatus_upie = mstatus_reg[4];
    wire mstatus_mie = mstatus_reg[3];
    wire mstatus_sie = mstatus_reg[1];
    wire mstatus_uie = mstatus_reg[0];

    reg [63:0] csr_old;
    always @(*) begin
        case (csr_addr)
            CSR_MSTATUS:    csr_old = mstatus_reg;
            CSR_MISA:       csr_old = misa_value;
            CSR_MEDELEG:    csr_old = medeleg_reg;
            CSR_MIDELEG:    csr_old = mideleg_reg;
            CSR_MIE:        csr_old = mie_reg;
            CSR_MTVEC:      csr_old = mtvec_reg;
            CSR_MCOUNTEREN: csr_old = mcounteren_reg;
            CSR_MSCRATCH:   csr_old = mscratch_reg;
            CSR_MEPC:       csr_old = mepc_reg;
            CSR_MCAUSE:     csr_old = mcause_reg;
            CSR_MTVAL:      csr_old = mtval_reg;
            CSR_MIP:        csr_old = mip_reg;
            CSR_MCYCLE:     csr_old = mcycle_reg;
            CSR_MINSTRET:   csr_old = minstret_reg;
            CSR_MHARTID:    csr_old = mhartid_reg;
            CSR_MVENDORID:  csr_old = mvendorid_reg;
            CSR_MARCHID:    csr_old = marchid_reg;
            CSR_MIMPID:     csr_old = mimpid_reg;
            CSR_SSTATUS:    csr_old = mstatus_reg & 64'h80000003000DE762;
            CSR_SIE:        csr_old = mie_reg & mideleg_reg;
            CSR_STVEC:      csr_old = stvec_reg;
            CSR_SSCRATCH:   csr_old = sscratch_reg;
            CSR_SEPC:       csr_old = sepc_reg;
            CSR_SCAUSE:     csr_old = scause_reg;
            CSR_STVAL:      csr_old = stval_reg;
            CSR_SIP:        csr_old = mip_reg & mideleg_reg;
            CSR_SATP:       csr_old = satp_reg;
            CSR_CYCLE:      csr_old = mcycle_reg;
            CSR_TIME:       csr_old = mcycle_reg;
            CSR_INSTRET:    csr_old = minstret_reg;
            default:        csr_old = 64'b0;
        endcase
    end

    wire [4:0] zimm = rs1;
    reg [63:0] csr_new;
    always @(*) begin
        csr_new = csr_old;
        case (funct3)
            3'b001: csr_new = src1;
            3'b010: csr_new = csr_old | src1;
            3'b011: csr_new = csr_old & ~src1;
            3'b101: csr_new = {59'b0, zimm};
            3'b110: csr_new = csr_old | {59'b0, zimm};
            3'b111: csr_new = csr_old & ~{59'b0, zimm};
            default: csr_new = csr_old;
        endcase
    end

    wire satp_mode = satp_reg[63:60] == 4'h8;
    wire [43:0] satp_ppn = satp_reg[43:0];
    wire [15:0] satp_asid = satp_reg[59:44];

    wire [1:0] eff_priv = (mstatus_mprv && (is_load || is_store)) ? mstatus_mpp : priv_mode;
    wire mmu_enable = satp_mode && (eff_priv != PRIV_M);

    reg [63:0] tlb_vaddr [0:15];
    reg [63:0] tlb_paddr [0:15];
    reg [15:0] tlb_valid;
    reg [15:0] tlb_asid [0:15];
    reg        tlb_user [0:15];
    reg        tlb_read [0:15];
    reg        tlb_write [0:15];
    reg        tlb_exec [0:15];
    reg        tlb_accessed [0:15];
    reg        tlb_dirty [0:15];
    integer    tlb_idx;

    wire [26:0] vpn_pc = pc[38:12];
    wire [11:0] offset_pc = pc[11:0];
    wire [26:0] vpn_mem = eff_addr[38:12];
    wire [11:0] offset_mem = eff_addr[11:0];

    reg [63:0] translated_pc;
    reg pc_fault;
    reg tlb_hit_pc;
    integer tlb_match_pc;

    always @(*) begin
        tlb_hit_pc = 0;
        tlb_match_pc = 0;
        translated_pc = pc;
        pc_fault = 0;
        
        if (mmu_enable) begin
            for (tlb_idx = 0; tlb_idx < 16; tlb_idx = tlb_idx + 1) begin
                if (tlb_valid[tlb_idx] && (tlb_vaddr[tlb_idx][38:12] == vpn_pc) && 
                    (tlb_asid[tlb_idx] == satp_asid || tlb_vaddr[tlb_idx][63])) begin
                    tlb_hit_pc = 1;
                    tlb_match_pc = tlb_idx;
                    if (tlb_exec[tlb_idx]) begin
                        translated_pc = {20'b0, tlb_paddr[tlb_idx][43:12], offset_pc};
                        pc_fault = 0;
                    end else begin
                        pc_fault = 1;
                    end
                end
            end
            if (!tlb_hit_pc) begin
                pc_fault = 1;
            end
        end
    end

    reg [63:0] translated_mem;
    reg mem_fault_load;
    reg mem_fault_store;
    reg tlb_hit_mem;
    integer tlb_match_mem;

    always @(*) begin
        tlb_hit_mem = 0;
        tlb_match_mem = 0;
        translated_mem = eff_addr;
        mem_fault_load = 0;
        mem_fault_store = 0;
        
        if (mmu_enable && (is_load || is_store || is_amo)) begin
            for (tlb_idx = 0; tlb_idx < 16; tlb_idx = tlb_idx + 1) begin
                if (tlb_valid[tlb_idx] && (tlb_vaddr[tlb_idx][38:12] == vpn_mem) && 
                    (tlb_asid[tlb_idx] == satp_asid || tlb_vaddr[tlb_idx][63])) begin
                    tlb_hit_mem = 1;
                    tlb_match_mem = tlb_idx;
                    if (is_load || is_amo) begin
                        if (tlb_read[tlb_idx] || (mstatus_mxr && tlb_exec[tlb_idx])) begin
                            if (eff_priv == PRIV_U && !tlb_user[tlb_idx]) begin
                                mem_fault_load = 1;
                            end else if (eff_priv == PRIV_S && tlb_user[tlb_idx] && !mstatus_sum) begin
                                mem_fault_load = 1;
                            end else begin
                                translated_mem = {20'b0, tlb_paddr[tlb_idx][43:12], offset_mem};
                                mem_fault_load = 0;
                            end
                        end else begin
                            mem_fault_load = 1;
                        end
                    end
                    if (is_store || is_amo) begin
                        if (tlb_write[tlb_idx]) begin
                            if (eff_priv == PRIV_U && !tlb_user[tlb_idx]) begin
                                mem_fault_store = 1;
                            end else if (eff_priv == PRIV_S && tlb_user[tlb_idx] && !mstatus_sum) begin
                                mem_fault_store = 1;
                            end else begin
                                translated_mem = {20'b0, tlb_paddr[tlb_idx][43:12], offset_mem};
                                mem_fault_store = 0;
                            end
                        end else begin
                            mem_fault_store = 1;
                        end
                    end
                end
            end
            if (!tlb_hit_mem) begin
                if (is_load || is_amo) mem_fault_load = 1;
                if (is_store || is_amo) mem_fault_store = 1;
            end
        end
    end

    assign phys_pc = translated_pc;
    assign page_fault_instr = pc_fault;
    assign page_fault_load = mem_fault_load;
    assign page_fault_store = mem_fault_store;

    wire [63:0] eff_addr = src1 + (is_store ? imm_s : (is_amo ? 64'b0 : imm_i));

    wire [2:0] addr_byte = translated_mem[2:0];
    wire [63:0] load_raw = mem_rdata;
    
    reg [63:0] load_data;
    always @(*) begin
        case (funct3)
            3'b000: begin
                case(addr_byte)
                    3'b000: load_data = {{56{load_raw[7]}}, load_raw[7:0]};
                    3'b001: load_data = {{56{load_raw[15]}}, load_raw[15:8]};
                    3'b010: load_data = {{56{load_raw[23]}}, load_raw[23:16]};
                    3'b011: load_data = {{56{load_raw[31]}}, load_raw[31:24]};
                    3'b100: load_data = {{56{load_raw[39]}}, load_raw[39:32]};
                    3'b101: load_data = {{56{load_raw[47]}}, load_raw[47:40]};
                    3'b110: load_data = {{56{load_raw[55]}}, load_raw[55:48]};
                    3'b111: load_data = {{56{load_raw[63]}}, load_raw[63:56]};
                endcase
            end
            3'b100: begin
                case(addr_byte)
                    3'b000: load_data = {56'b0, load_raw[7:0]};
                    3'b001: load_data = {56'b0, load_raw[15:8]};
                    3'b010: load_data = {56'b0, load_raw[23:16]};
                    3'b011: load_data = {56'b0, load_raw[31:24]};
                    3'b100: load_data = {56'b0, load_raw[39:32]};
                    3'b101: load_data = {56'b0, load_raw[47:40]};
                    3'b110: load_data = {56'b0, load_raw[55:48]};
                    3'b111: load_data = {56'b0, load_raw[63:56]};
                endcase
            end
            3'b001: begin
                case(addr_byte[2:1])
                    2'b00: load_data = {{48{load_raw[15]}}, load_raw[15:0]};
                    2'b01: load_data = {{48{load_raw[31]}}, load_raw[31:16]};
                    2'b10: load_data = {{48{load_raw[47]}}, load_raw[47:32]};
                    2'b11: load_data = {{48{load_raw[63]}}, load_raw[63:48]};
                endcase
            end
            3'b101: begin
                case(addr_byte[2:1])
                    2'b00: load_data = {48'b0, load_raw[15:0]};
                    2'b01: load_data = {48'b0, load_raw[31:16]};
                    2'b10: load_data = {48'b0, load_raw[47:32]};
                    2'b11: load_data = {48'b0, load_raw[63:48]};
                endcase
            end
            3'b010: begin
                case(addr_byte[2])
                    1'b0: load_data = {{32{load_raw[31]}}, load_raw[31:0]};
                    1'b1: load_data = {{32{load_raw[63]}}, load_raw[63:32]};
                endcase
            end
            3'b110: begin
                case(addr_byte[2])
                    1'b0: load_data = {32'b0, load_raw[31:0]};
                    1'b1: load_data = {32'b0, load_raw[63:32]};
                endcase
            end
            3'b011: load_data = load_raw;
            default: load_data = 64'b0;
        endcase
    end

    reg [7:0] wstrb_comb;
    reg [63:0] wdata_shifted;
    always @(*) begin
        wstrb_comb = 8'b0000_0000;
        wdata_shifted = src2_reg;
        if (is_store) begin
            case (funct3)
                3'b000: begin
                    wstrb_comb = 8'b0000_0001 << addr_byte;
                    wdata_shifted = {8{src2_reg[7:0]}};
                end
                3'b001: begin
                    wstrb_comb = (addr_byte[2] ? 8'b1100_0000 : (addr_byte[1] ? 8'b0000_1100 : 8'b0000_0011));
                    wdata_shifted = {4{src2_reg[15:0]}};
                end
                3'b010: begin
                    wstrb_comb = addr_byte[2] ? 8'b1111_0000 : 8'b0000_1111;
                    wdata_shifted = {2{src2_reg[31:0]}};
                end
                3'b011: begin
                    wstrb_comb = 8'b1111_1111;
                    wdata_shifted = src2_reg;
                end
                default: wstrb_comb = 8'b0000_0000;
            endcase
        end
    end

    wire amo_op = is_amo && (funct3 == 3'b011 || funct3 == 3'b010);
    wire [4:0] amo_funct = instr[31:27];
    wire amo_aq = instr[26];
    wire amo_rl = instr[25];
    wire is_lr = is_amo && (amo_funct == 5'b00010);
    wire is_sc = is_amo && (amo_funct == 5'b00011);
    
    reg [63:0] reservation_addr;
    reg reservation_valid;
    
    reg [63:0] amo_result;
    reg [63:0] amo_store_data;
    always @(*) begin
        if (funct3 == 3'b010) begin
            case(amo_funct)
                5'b00010: begin
                    amo_result = {{32{load_data[31]}}, load_data[31:0]};
                    amo_store_data = {{32{src2_reg[31]}}, src2_reg[31:0]};
                end
                5'b00011: begin
                    amo_result = reservation_valid && (reservation_addr == translated_mem) ? 64'b0 : 64'b1;
                    amo_store_data = {{32{src2_reg[31]}}, src2_reg[31:0]};
                end
                5'b00000: begin
                    amo_result = {{32{load_data[31]}}, load_data[31:0]};
                    amo_store_data = {{32{(load_data[31:0] + src2_reg[31:0])[31]}}, load_data[31:0] + src2_reg[31:0]};
                end
                5'b00100: begin
                    amo_result = {{32{load_data[31]}}, load_data[31:0]};
                    amo_store_data = {{32{(load_data[31:0] ^ src2_reg[31:0])[31]}}, load_data[31:0] ^ src2_reg[31:0]};
                end
                5'b01100: begin
                    amo_result = {{32{load_data[31]}}, load_data[31:0]};
                    amo_store_data = {{32{(load_data[31:0] & src2_reg[31:0])[31]}}, load_data[31:0] & src2_reg[31:0]};
                end
                5'b01000: begin
                    amo_result = {{32{load_data[31]}}, load_data[31:0]};
                    amo_store_data = {{32{(load_data[31:0] | src2_reg[31:0])[31]}}, load_data[31:0] | src2_reg[31:0]};
                end
                5'b10000: begin
                    amo_result = {{32{load_data[31]}}, load_data[31:0]};
                    amo_store_data = ($signed(load_data[31:0]) < $signed(src2_reg[31:0])) ? {{32{load_data[31]}}, load_data[31:0]} : {{32{src2_reg[31]}}, src2_reg[31:0]};
                end
                5'b10100: begin
                    amo_result = {{32{load_data[31]}}, load_data[31:0]};
                    amo_store_data = ($signed(load_data[31:0]) > $signed(src2_reg[31:0])) ? {{32{load_data[31]}}, load_data[31:0]} : {{32{src2_reg[31]}}, src2_reg[31:0]};
                end
                5'b11000: begin
                    amo_result = {{32{load_data[31]}}, load_data[31:0]};
                    amo_store_data = (load_data[31:0] < src2_reg[31:0]) ? {{32{load_data[31]}}, load_data[31:0]} : {{32{src2_reg[31]}}, src2_reg[31:0]};
                end
                5'b11100: begin
                    amo_result = {{32{load_data[31]}}, load_data[31:0]};
                    amo_store_data = (load_data[31:0] > src2_reg[31:0]) ? {{32{load_data[31]}}, load_data[31:0]} : {{32{src2_reg[31]}}, src2_reg[31:0]};
                end
                default: begin
                    amo_result = {{32{load_data[31]}}, load_data[31:0]};
                    amo_store_data = {{32{src2_reg[31]}}, src2_reg[31:0]};
                end
            endcase
        end else begin
            case(amo_funct)
                5'b00010: begin
                    amo_result = load_data;
                    amo_store_data = src2_reg;
                end
                5'b00011: begin
                    amo_result = reservation_valid && (reservation_addr == translated_mem) ? 64'b0 : 64'b1;
                    amo_store_data = src2_reg;
                end
                5'b00000: begin
                    amo_result = load_data;
                    amo_store_data = load_data + src2_reg;
                end
                5'b00100: begin
                    amo_result = load_data;
                    amo_store_data = load_data ^ src2_reg;
                end
                5'b01100: begin
                    amo_result = load_data;
                    amo_store_data = load_data & src2_reg;
                end
                5'b01000: begin
                    amo_result = load_data;
                    amo_store_data = load_data | src2_reg;
                end
                5'b10000: begin
                    amo_result = load_data;
                    amo_store_data = ($signed(load_data) < $signed(src2_reg)) ? load_data : src2_reg;
                end
                5'b10100: begin
                    amo_result = load_data;
                    amo_store_data = ($signed(load_data) > $signed(src2_reg)) ? load_data : src2_reg;
                end
                5'b11000: begin
                    amo_result = load_data;
                    amo_store_data = (load_data < src2_reg) ? load_data : src2_reg;
                end
                5'b11100: begin
                    amo_result = load_data;
                    amo_store_data = (load_data > src2_reg) ? load_data : src2_reg;
                end
                default: begin
                    amo_result = load_data;
                    amo_store_data = src2_reg;
                end
            endcase
        end
    end

    reg mem_req_pending;
    reg is_load_pending;
    reg is_amo_pending;
    reg amo_need_store;
    reg [4:0] rd_pending;
    reg [2:0] funct3_pending;
    reg [63:0] amo_wdata_pending;
    reg ptw_active;
    reg [1:0] ptw_level;
    reg [63:0] ptw_addr;
    reg [63:0] ptw_vaddr;
    reg ptw_for_pc;
    reg ptw_for_load;
    reg ptw_for_store;

    wire misalign_lh = is_load && (funct3 == 3'b001 || funct3 == 3'b101) && eff_addr[0];
    wire misalign_lw = is_load && (funct3 == 3'b010 || funct3 == 3'b110) && (eff_addr[1:0] != 2'b00);
    wire misalign_ld = is_load && (funct3 == 3'b011) && (eff_addr[2:0] != 3'b000);
    wire misalign_sh = is_store && (funct3 == 3'b001) && eff_addr[0];
    wire misalign_sw = is_store && (funct3 == 3'b010) && (eff_addr[1:0] != 2'b00);
    wire misalign_sd = is_store && (funct3 == 3'b011) && (eff_addr[2:0] != 3'b000);
    wire misalign = misalign_lh | misalign_lw | misalign_ld | misalign_sh | misalign_sw | misalign_sd;

    wire [63:0] misalign_cause = is_load ? 64'd4 : 64'd6;
    wire [63:0] page_fault_cause = (is_load || is_amo) ? 64'd13 : (is_store ? 64'd15 : 64'd12);

    wire illegal_priv = (priv_mode != PRIV_M) && 
                       ((is_mret) ||
                        (is_sret && priv_mode == PRIV_U) ||
                        (is_wfi && priv_mode == PRIV_U && mstatus_tw) ||
                        (is_sfence_vma && priv_mode == PRIV_S && mstatus_tvm));

    wire illegal_csr = is_csr && 
                      ((csr_addr[9:8] > priv_mode) ||
                       (csr_addr[11:10] == 2'b11 && funct3[1]));

    wire illegal_op = ~(is_op_imm | is_op | is_op_imm32 | is_op32 | is_lui | is_auipc | is_load | is_store | is_branch | is_jal | is_jalr | is_system | is_amo | is_fence);

    wire page_fault = (pc_fault && !ptw_active) || (mem_fault_load && is_load) || (mem_fault_store && is_store);

    wire take_trap = is_ecall | is_ebreak | illegal_op | illegal_priv | illegal_csr | misalign | page_fault;
    wire [63:0] trap_cause = is_ecall ? (priv_mode == PRIV_U ? 64'd8 : (priv_mode == PRIV_S ? 64'd9 : 64'd11)) : 
                            (is_ebreak ? 64'd3 : 
                            (page_fault ? page_fault_cause :
                            (misalign ? misalign_cause : 64'd2)));

    wire delegate_to_s = (priv_mode != PRIV_M) && medeleg_reg[trap_cause[3:0]];
    wire [63:0] trap_vec = delegate_to_s ? stvec_reg : mtvec_reg;
    wire [63:0] trap_pc = trap_vec[1:0] == 2'b01 ? {trap_vec[63:2], 2'b00} + (trap_cause << 2) : {trap_vec[63:2], 2'b00};

    reg [3:0] tlb_replace_ptr;

    always @(posedge clk or posedge reset) begin
        if (reset) begin
            pc <= 64'h8000_0000;
            mem_wen <= 1'b0;
            mem_valid <= 1'b0;
            mem_addr <= 64'b0;
            mem_wdata <= 64'b0;
            mem_wstrb <= 8'b0;
            priv_mode <= PRIV_M;
            mstatus_reg <= 64'h0000_0000_0000_1800;
            medeleg_reg <= 64'b0;
            mideleg_reg <= 64'b0;
            mie_reg <= 64'b0;
            mtvec_reg <= 64'b0;
            mscratch_reg <= 64'b0;
            mepc_reg <= 64'b0;
            mcause_reg <= 64'b0;
            mtval_reg <= 64'b0;
            mip_reg <= 64'b0;
            mcounteren_reg <= 64'b0;
            mcycle_reg <= 64'b0;
            minstret_reg <= 64'b0;
            mhartid_reg <= 64'b0;
            mvendorid_reg <= 64'b0;
            marchid_reg <= 64'b0;
            mimpid_reg <= 64'b0;
            stvec_reg <= 64'b0;
            sscratch_reg <= 64'b0;
            sepc_reg <= 64'b0;
            scause_reg <= 64'b0;
            stval_reg <= 64'b0;
            satp_reg <= 64'b0;
            mem_req_pending <= 1'b0;
            is_load_pending <= 1'b0;
            is_amo_pending <= 1'b0;
            amo_need_store <= 1'b0;
            rd_pending <= 5'b0;
            funct3_pending <= 3'b0;
            amo_wdata_pending <= 64'b0;
            reservation_valid <= 1'b0;
            reservation_addr <= 64'b0;
            tlb_valid <= 16'b0;
            tlb_replace_ptr <= 4'b0;
            ptw_active <= 1'b0;
            ptw_level <= 2'b0;
            ptw_addr <= 64'b0;
            ptw_vaddr <= 64'b0;
            ptw_for_pc <= 1'b0;
            ptw_for_load <= 1'b0;
            ptw_for_store <= 1'b0;
            for (i=0; i<32; i=i+1) regs[i] <= 64'b0;
            for (i=0; i<16; i=i+1) begin
                tlb_vaddr[i] <= 64'b0;
                tlb_paddr[i] <= 64'b0;
                tlb_asid[i] <= 16'b0;
                tlb_user[i] <= 1'b0;
                tlb_read[i] <= 1'b0;
                tlb_write[i] <= 1'b0;
                tlb_exec[i] <= 1'b0;
                tlb_accessed[i] <= 1'b0;
                tlb_dirty[i] <= 1'b0;
            end
        end else begin
            mem_wen <= 1'b0;
            mem_valid <= 1'b0;
            mem_wstrb <= 8'b0;
            mcycle_reg <= mcycle_reg + 64'b1;

            if (ptw_active) begin
                if (mem_ready) begin
                    wire [63:0] pte = mem_rdata;
                    wire pte_v = pte[0];
                    wire pte_r = pte[1];
                    wire pte_w = pte[2];
                    wire pte_x = pte[3];
                    wire pte_u = pte[4];
                    wire pte_g = pte[5];
                    wire pte_a = pte[6];
                    wire pte_d = pte[7];
                    wire [43:0] pte_ppn = pte[53:10];
                    
                    if (!pte_v || (!pte_r && pte_w)) begin
                        ptw_active <= 1'b0;
                        mepc_reg <= pc;
                        mcause_reg <= ptw_for_pc ? 64'd12 : (ptw_for_load ? 64'd13 : 64'd15);
                        mtval_reg <= ptw_vaddr;
                        if (delegate_to_s) begin
                            sepc_reg <= pc;
                            scause_reg <= ptw_for_pc ? 64'd12 : (ptw_for_load ? 64'd13 : 64'd15);
                            stval_reg <= ptw_vaddr;
                            mstatus_reg[8] <= priv_mode[0];
                            mstatus_reg[5] <= mstatus_reg[1];
                            mstatus_reg[1] <= 1'b0;
                            priv_mode <= PRIV_S;
                            pc <= trap_pc;
                        end else begin
                            mstatus_reg[12:11] <= priv_mode;
                            mstatus_reg[7] <= mstatus_reg[3];
                            mstatus_reg[3] <= 1'b0;
                            priv_mode <= PRIV_M;
                            pc <= trap_pc;
                        end
                    end else if (pte_r || pte_x) begin
                        tlb_vaddr[tlb_replace_ptr] <= ptw_vaddr;
                        tlb_paddr[tlb_replace_ptr] <= {20'b0, pte_ppn};
                        tlb_asid[tlb_replace_ptr] <= satp_asid;
                        tlb_user[tlb_replace_ptr] <= pte_u;
                        tlb_read[tlb_replace_ptr] <= pte_r;
                        tlb_write[tlb_replace_ptr] <= pte_w;
                        tlb_exec[tlb_replace_ptr] <= pte_x;
                        tlb_accessed[tlb_replace_ptr] <= pte_a;
                        tlb_dirty[tlb_replace_ptr] <= pte_d;
                        tlb_valid[tlb_replace_ptr] <= 1'b1;
                        tlb_replace_ptr <= tlb_replace_ptr + 1;
                        ptw_active <= 1'b0;
                    end else begin
                        if (ptw_level == 2'b00) begin
                            ptw_active <= 1'b0;
                            mepc_reg <= pc;
                            mcause_reg <= ptw_for_pc ? 64'd12 : (ptw_for_load ? 64'd13 : 64'd15);
                            mtval_reg <= ptw_vaddr;
                            if (delegate_to_s) begin
                                sepc_reg <= pc;
                                scause_reg <= ptw_for_pc ? 64'd12 : (ptw_for_load ? 64'd13 : 64'd15);
                                stval_reg <= ptw_vaddr;
                                mstatus_reg[8] <= priv_mode[0];
                                mstatus_reg[5] <= mstatus_reg[1];
                                mstatus_reg[1] <= 1'b0;
                                priv_mode <= PRIV_S;
                                pc <= trap_pc;
                            end else begin
                                mstatus_reg[12:11] <= priv_mode;
                                mstatus_reg[7] <= mstatus_reg[3];
                                mstatus_reg[3] <= 1'b0;
                                priv_mode <= PRIV_M;
                                pc <= trap_pc;
                            end
                        end else begin
                            ptw_level <= ptw_level - 1;
                            case(ptw_level)
                                2'b10: ptw_addr <= {20'b0, pte_ppn, ptw_vaddr[29:21], 3'b000};
                                2'b01: ptw_addr <= {20'b0, pte_ppn, ptw_vaddr[20:12], 3'b000};
                                default: ptw_addr <= 64'b0;
                            endcase
                            mem_addr <= ptw_addr;
                            mem_valid <= 1'b1;
                            mem_wen <= 1'b0;
                        end
                    end
                end else begin
                    mem_addr <= ptw_addr;
                    mem_valid <= 1'b1;
                    mem_wen <= 1'b0;
                end
            end else if (take_trap) begin
                if (delegate_to_s) begin
                    sepc_reg <= pc;
                    scause_reg <= trap_cause;
                    stval_reg <= page_fault ? (pc_fault ? pc : eff_addr) : (misalign ? eff_addr : 64'b0);
                    mstatus_reg[8] <= priv_mode[0];
                    mstatus_reg[5] <= mstatus_reg[1];
                    mstatus_reg[1] <= 1'b0;
                    priv_mode <= PRIV_S;
                    pc <= trap_pc;
                end else begin
                    mepc_reg <= pc;
                    mcause_reg <= trap_cause;
                    mtval_reg <= page_fault ? (pc_fault ? pc : eff_addr) : (misalign ? eff_addr : 64'b0);
                    mstatus_reg[12:11] <= priv_mode;
                    mstatus_reg[7] <= mstatus_reg[3];
                    mstatus_reg[3] <= 1'b0;
                    priv_mode <= PRIV_M;
                    pc <= trap_pc;
                end
                mem_req_pending <= 1'b0;
                is_load_pending <= 1'b0;
                is_amo_pending <= 1'b0;
                amo_need_store <= 1'b0;
                reservation_valid <= 1'b0;
            end else if (is_mret) begin
                mstatus_reg[3] <= mstatus_reg[7];
                mstatus_reg[7] <= 1'b1;
                priv_mode <= mstatus_reg[12:11];
                mstatus_reg[12:11] <= 2'b00;
                pc <= mepc_reg;
                minstret_reg <= minstret_reg + 64'b1;
            end else if (is_sret) begin
                mstatus_reg[1] <= mstatus_reg[5];
                mstatus_reg[5] <= 1'b1;
                priv_mode <= {1'b0, mstatus_reg[8]};
                mstatus_reg[8] <= 1'b0;
                pc <= sepc_reg;
                minstret_reg <= minstret_reg + 64'b1;
            end else if (is_wfi) begin
                pc <= pc + 64'd4;
                minstret_reg <= minstret_reg + 64'b1;
            end else if (is_sfence_vma) begin
                if (rs1 == 0 && rs2 == 0) begin
                    tlb_valid <= 16'b0;
                end else if (rs2 == 0) begin
                    for (i = 0; i < 16; i = i + 1) begin
                        if (tlb_vaddr[i][38:12] == src1[26:0]) begin
                            tlb_valid[i] <= 1'b0;
                        end
                    end
                end else if (rs1 == 0) begin
                    for (i = 0; i < 16; i = i + 1) begin
                        if (tlb_asid[i] == src2_reg[15:0]) begin
                            tlb_valid[i] <= 1'b0;
                        end
                    end
                end else begin
                    for (i = 0; i < 16; i = i + 1) begin
                        if (tlb_vaddr[i][38:12] == src1[26:0] && tlb_asid[i] == src2_reg[15:0]) begin
                            tlb_valid[i] <= 1'b0;
                        end
                    end
                end
                pc <= pc + 64'd4;
                minstret_reg <= minstret_reg + 64'b1;
            end else if (pc_fault && !tlb_hit_pc) begin
                ptw_active <= 1'b1;
                ptw_level <= 2'b10;
                ptw_vaddr <= pc;
                ptw_addr <= {20'b0, satp_ppn, pc[38:30], 3'b000};
                ptw_for_pc <= 1'b1;
                ptw_for_load <= 1'b0;
                ptw_for_store <= 1'b0;
                mem_addr <= {20'b0, satp_ppn, pc[38:30], 3'b000};
                mem_valid <= 1'b1;
                mem_wen <= 1'b0;
            end else if (mem_req_pending) begin
                if (mem_ready) begin
                    if (is_load_pending && rd_pending != 0) begin
                        regs[rd_pending] <= load_data;
                    end
                    if (is_amo_pending) begin
                        if (amo_need_store) begin
                            if (is_sc && !(reservation_valid && (reservation_addr == translated_mem))) begin
                                if (rd_pending != 0) regs[rd_pending] <= 64'b1;
                                mem_req_pending <= 1'b0;
                                is_amo_pending <= 1'b0;
                                pc <= pc + 64'd4;
                                minstret_reg <= minstret_reg + 64'b1;
                            end else begin
                                mem_addr <= translated_mem;
                                mem_wdata <= amo_wdata_pending;
                                mem_wstrb <= (funct3_pending == 3'b010) ? 8'b0000_1111 : 8'b1111_1111;
                                mem_wen <= 1'b1;
                                mem_valid <= 1'b1;
                                amo_need_store <= 1'b0;
                                reservation_valid <= 1'b0;
                            end
                        end else begin
                            if (rd_pending != 0) regs[rd_pending] <= is_sc ? 64'b0 : amo_result;
                            mem_req_pending <= 1'b0;
                            is_amo_pending <= 1'b0;
                            pc <= pc + 64'd4;
                            minstret_reg <= minstret_reg + 64'b1;
                        end
                    end else begin
                        mem_req_pending <= 1'b0;
                        is_load_pending <= 1'b0;
                        pc <= pc + 64'd4;
                        minstret_reg <= minstret_reg + 64'b1;
                    end
                end
            end else if (is_jal) begin
                if (rd != 0) regs[rd] <= pc + 64'd4;
                pc <= pc + imm_j;
                minstret_reg <= minstret_reg + 64'b1;
            end else if (is_jalr) begin
                if (rd != 0) regs[rd] <= pc + 64'd4;
                pc <= (src1 + imm_i) & ~64'd1;
                minstret_reg <= minstret_reg + 64'b1;
            end else if (is_branch) begin
                pc <= branch_taken ? (pc + imm_b) : (pc + 64'd4);
                minstret_reg <= minstret_reg + 64'b1;
            end else if (is_fence) begin
                pc <= pc + 64'd4;
                minstret_reg <= minstret_reg + 64'b1;
            end else begin
                if (is_lui || is_auipc || is_op_imm || is_op || is_op_imm32 || is_op32) begin
                    if (rd != 0) regs[rd] <= alu_result;
                end
                if (is_csr) begin
                    if (rd != 0) regs[rd] <= csr_old;
                    case (csr_addr)
                        CSR_MSTATUS: begin
                            mstatus_reg[12:11] <= csr_new[12:11];
                            mstatus_reg[8] <= csr_new[8];
                            mstatus_reg[7] <= csr_new[7];
                            mstatus_reg[5] <= csr_new[5];
                            mstatus_reg[4] <= csr_new[4];
                            mstatus_reg[3] <= csr_new[3];
                            mstatus_reg[1] <= csr_new[1];
                            mstatus_reg[0] <= csr_new[0];
                            mstatus_reg[22] <= csr_new[22];
                            mstatus_reg[21] <= csr_new[21];
                            mstatus_reg[20] <= csr_new[20];
                            mstatus_reg[19] <= csr_new[19];
                            mstatus_reg[18] <= csr_new[18];
                            mstatus_reg[17] <= csr_new[17];
                        end
                        CSR_MEDELEG: medeleg_reg <= csr_new & 64'hB3FF;
                        CSR_MIDELEG: mideleg_reg <= csr_new & 64'h0222;
                        CSR_MIE: mie_reg <= csr_new;
                        CSR_MTVEC: mtvec_reg <= {csr_new[63:2], 2'b00};
                        CSR_MCOUNTEREN: mcounteren_reg <= csr_new;
                        CSR_MSCRATCH: mscratch_reg <= csr_new;
                        CSR_MEPC: mepc_reg <= csr_new;
                        CSR_MCAUSE: mcause_reg <= csr_new;
                        CSR_MTVAL: mtval_reg <= csr_new;
                        CSR_MIP: mip_reg <= csr_new;
                        CSR_SSTATUS: begin
                            mstatus_reg[8] <= csr_new[8];
                            mstatus_reg[5] <= csr_new[5];
                            mstatus_reg[1] <= csr_new[1];
                            mstatus_reg[19] <= csr_new[19];
                            mstatus_reg[18] <= csr_new[18];
                        end
                        CSR_SIE: mie_reg <= (mie_reg & ~mideleg_reg) | (csr_new & mideleg_reg);
                        CSR_STVEC: stvec_reg <= {csr_new[63:2], 2'b00};
                        CSR_SSCRATCH: sscratch_reg <= csr_new;
                        CSR_SEPC: sepc_reg <= csr_new;
                        CSR_SCAUSE: scause_reg <= csr_new;
                        CSR_STVAL: stval_reg <= csr_new;
                        CSR_SIP: mip_reg <= (mip_reg & ~mideleg_reg) | (csr_new & mideleg_reg);
                        CSR_SATP: begin
                            if (priv_mode == PRIV_M || !mstatus_tvm) begin
                                satp_reg <= csr_new;
                                tlb_valid <= 16'b0;
                            end
                        end
                    endcase
                end
                if (is_load || is_store || is_amo) begin
                    if ((mem_fault_load && is_load) || (mem_fault_store && is_store)) begin
                        if (!tlb_hit_mem && mmu_enable) begin
                            ptw_active <= 1'b1;
                            ptw_level <= 2'b10;
                            ptw_vaddr <= eff_addr;
                            ptw_addr <= {20'b0, satp_ppn, eff_addr[38:30], 3'b000};
                            ptw_for_pc <= 1'b0;
                            ptw_for_load <= is_load;
                            ptw_for_store <= is_store;
                            mem_addr <= {20'b0, satp_ppn, eff_addr[38:30], 3'b000};
                            mem_valid <= 1'b1;
                            mem_wen <= 1'b0;
                        end
                    end else if (!misalign) begin
                        mem_addr <= translated_mem;
                        if (is_store) begin
                            mem_wdata <= wdata_shifted;
                            mem_wstrb <= wstrb_comb;
                            mem_wen <= 1'b1;
                            mem_valid <= 1'b1;
                            mem_req_pending <= 1'b1;
                            is_load_pending <= 1'b0;
                            is_amo_pending <= 1'b0;
                            rd_pending <= 5'b0;
                            reservation_valid <= 1'b0;
                        end else if (is_amo) begin
                            if (is_lr) begin
                                reservation_addr <= translated_mem;
                                reservation_valid <= 1'b1;
                                mem_wen <= 1'b0;
                                mem_wstrb <= 8'b0;
                                mem_valid <= 1'b1;
                                mem_req_pending <= 1'b1;
                                is_load_pending <= 1'b1;
                                is_amo_pending <= 1'b0;
                                rd_pending <= rd;
                                funct3_pending <= funct3;
                            end else if (is_sc) begin
                                if (reservation_valid && (reservation_addr == translated_mem)) begin
                                    mem_wdata <= wdata_shifted;
                                    mem_wstrb <= (funct3 == 3'b010) ? 8'b0000_1111 : 8'b1111_1111;
                                    mem_wen <= 1'b1;
                                    mem_valid <= 1'b1;
                                    mem_req_pending <= 1'b1;
                                    is_load_pending <= 1'b0;
                                    is_amo_pending <= 1'b1;
                                    amo_need_store <= 1'b0;
                                    rd_pending <= rd;
                                    funct3_pending <= funct3;
                                    amo_wdata_pending <= src2_reg;
                                    reservation_valid <= 1'b0;
                                end else begin
                                    if (rd != 0) regs[rd] <= 64'b1;
                                    pc <= pc + 64'd4;
                                    minstret_reg <= minstret_reg + 64'b1;
                                end
                            end else begin
                                mem_wen <= 1'b0;
                                mem_wstrb <= 8'b0;
                                mem_valid <= 1'b1;
                                mem_req_pending <= 1'b1;
                                is_load_pending <= 1'b0;
                                is_amo_pending <= 1'b1;
                                amo_need_store <= 1'b1;
                                rd_pending <= rd;
                                funct3_pending <= funct3;
                                amo_wdata_pending <= amo_store_data;
                                reservation_valid <= 1'b0;
                            end
                        end else begin
                            mem_wen <= 1'b0;
                            mem_wstrb <= 8'b0;
                            mem_valid <= 1'b1;
                            mem_req_pending <= 1'b1;
                            is_load_pending <= 1'b1;
                            is_amo_pending <= 1'b0;
                            rd_pending <= rd;
                            funct3_pending <= funct3;
                        end
                    end
                end else begin
                    pc <= pc + 64'd4;
                    minstret_reg <= minstret_reg + 64'b1;
                end
            end
            regs[0] <= 64'b0;
        end
    end

endmodule
