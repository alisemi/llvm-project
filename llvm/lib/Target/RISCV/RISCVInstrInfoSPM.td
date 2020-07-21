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
//def OPC_SPM_MEM : RISCVOpcode<0b0110011>; //Same as OPC_OP

let hasSideEffects = 1, mayLoad = 1, mayStore = 1 in
class SPM_rr<bits<7> funct7, bits<3> funct3, string opcodestr>
    : RVInstR<funct7, funct3, OPC_SPM, (outs GPR:$rd), (ins GPR:$rs1, GPR:$rs2),
              opcodestr, "$rd, $rs1, $rs2">;
let hasSideEffects = 1, mayLoad = 1, mayStore = 1 in
class SPM_ri<bits<3> funct3, string opcodestr>
    : RVInstI<funct3, OPC_SPM, (outs GPR:$rs2), (ins GPR:$rs1, simm12:$imm12),
              opcodestr, "$rs2, ${imm12}(${rs1})">;
let hasSideEffects = 1, mayLoad = 1, mayStore = 1 in
class SPM_load<bits<7> funct7, bits<3> funct3, string opcodestr>
    : RVInstR<funct7, funct3, OPC_OP, (outs GPR:$rd), (ins GPR:$rs1, GPR:$rs2),
              opcodestr, "$rd, $rs1, $rs2">;

class RVBInstFunct12<bits<12> funct12, bits<3> funct3, RISCVOpcode opcode,
                     string opcodestr>
    : RVInst<(outs GPR:$rd), (ins GPR:$rs1),
             opcodestr, "$rd, $rs1", [], InstFormatI> {
  bits<5> rs1;
  bits<5> rd;

  let Inst{31-20} = funct12;
  let Inst{19-15} = rs1;
  let Inst{14-12} = funct3;
  let Inst{11-7} = rd;
  let Opcode = opcode.Value;
}

//===----------------------------------------------------------------------===//
// Instructions
//===----------------------------------------------------------------------===//

let Predicates = [HasExtSPM] in {
def MEMSPM  : SPM_load<0b1000000, 0b000, "memspm">,
              Sched<[WriteSTW, ReadStoreData, ReadMemBase]>;
def SPMREG  : SPM_ri<0b000,"spmreg">,
              Sched<[]>; //Schudule Information??
def SPMDEL  : SPM_rr<0b0000000, 0b010, "spmdel">,
              Sched<[]>; //Schedule Information??
} // Predicates = [HasExtSPM]


//===----------------------------------------------------------------------===//
// Pseudo-instructions and codegen patterns
//===----------------------------------------------------------------------===//

//def : Pat<(prefetch GPR:$addr, imm:$imm, (i32 0), (i32 1)), (SPMREG GPR:$addr, imm:$imm)>;
def : Pat<(int_memspm GPR:$addr, GPR:$rs2), (MEMSPM GPR:$addr, GPR:$rs2)>;
def : Pat<(int_spmreg GPR:$addr, simm12:$imm12), (SPMREG GPR:$addr, simm12:$imm12)>;
def : Pat<(int_spmdel GPR:$addr, GPR:$rs2), (SPMDEL GPR:$addr, GPR:$rs2)>;

//def : Pat<(prefetch addr:$src, imm, (i32 0), (i32 1)), (MEMSPM X0, simm12:$imm)>;
