//===----------------------------------------------------------------------===//
//
// This file describes the RISC-V instructions from the 'SPM', SPM
// instruction set extension.
//
//===----------------------------------------------------------------------===//


//===----------------------------------------------------------------------===//
// Instruction class templates
//===----------------------------------------------------------------------===//
//SPM Opcode
def OPC_SPM     : RISCVOpcode<0b0001011>;
def OPC_SPM_MEM : RISCVOpcode<0b0110011>; //Same as OPC_OP

let hasSideEffects = 1, mayLoad = 0, mayStore = 0 in
class SPM_rr<bits<7> funct7, bits<3> funct3, string opcodestr>
    : RVInstR<funct7, funct3, OPC_SPM, (outs GPR:$rd), (ins GPR:$rs1, GPR:$rs2),
              opcodestr, "$rd, $rs1, $rs2">;

//let hasSideEffects = 1, mayLoad = 0, mayStore = 0 in
//class SPM_MEM_rr<bits<7> funct7, bits<3> funct3, string opcodestr>
//    : RVInstR<funct7, funct3, OPC_SPM_MEM, (outs GPR:$rd), (ins GPR:$rs1, GPR:$rs2),
//              opcodestr, "$rd, $rs1, $rs2">;

let hasSideEffects = 0, mayLoad = 1, mayStore = 0 in
class SPM_ri<bits<3> funct3, string opcodestr>
    : RVInstI<funct3, OPC_SPM, (outs GPR:$rd), (ins GPR:$rs1, simm12:$imm12),
              opcodestr, "$rd, ${imm12}(${rs1})">;


//===----------------------------------------------------------------------===//
// Instructions
//===----------------------------------------------------------------------===//

let Predicates = [HasExtSPM] in {
def SPMCON  : SPM_rr<0b0000000, 0b011, "spmcon">,
//              Sched<[WriteSTW, ReadStoreData, ReadMemBase]>;
              Sched<[WriteIALU, ReadIALU, ReadIALU]>;
//def MEMSPM  : SPM_rr<0b0000000, 0b100, "memspm">,
//              Sched<[WriteSTW, ReadStoreData, ReadMemBase]>;
let hasSideEffects = 1, mayLoad = 0, mayStore = 0 in
def MEMSPM  : ALU_rr<0b1000000, 0b000, "memspm">, 
//              Sched<[WriteSTW, ReadStoreData, ReadMemBase,WriteIALU, ReadIALU, ReadIALU]>;
             Sched<[WriteIALU, ReadIALU, ReadIALU]>;
def SPMREG  : SPM_ri<0b000,"spmreg">,
              //Sched<[]>; //Schudule Information??
              Sched<[WriteLDW, ReadMemBase]>;
def SPMDEL  : SPM_rr<0b0000000, 0b010, "spmdel">,
              Sched<[WriteIALU, ReadIALU, ReadIALU]>;
} // Predicates = [HasExtSPM]


//===----------------------------------------------------------------------===//
// Pseudo-instructions and codegen patterns
//===----------------------------------------------------------------------===//

//def : Pat<(prefetch GPR:$addr, imm:$imm, (i32 0), (i32 1)), (SPMREG GPR:$addr, imm:$imm)>;
def : Pat<(int_spmcon GPR:$addr, GPR:$rs2), (SPMCON GPR:$addr, GPR:$rs2)>;
def : Pat<(int_memspm GPR:$addr, GPR:$rs2), (MEMSPM GPR:$addr, GPR:$rs2)>;
def : Pat<(int_spmreg GPR:$addr, simm12:$imm12), (SPMREG GPR:$addr, simm12:$imm12)>;
def : Pat<(int_spmdel GPR:$addr, GPR:$rs2), (SPMDEL GPR:$addr, GPR:$rs2)>;

def : InstAlias<"spmreg $rd, 0(${rs1})",
                (SPMREG  GPR:$rd, GPR:$rs1, 0)>;
def : InstAlias<"spmreg $rd, $rs1, $imm12",
                (SPMREG  GPR:$rd, GPR:$rs1, simm12:$imm12)>;
