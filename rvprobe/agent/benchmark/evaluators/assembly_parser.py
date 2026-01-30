"""
Assembly Parser for RISC-V instructions.

Parses assembly instructions into structured format for constraint checking.
"""

import re
from typing import List, Dict, Optional, Any
from dataclasses import dataclass


@dataclass
class ParsedInstruction:
    """Structured representation of a parsed RISC-V instruction."""

    index: int  # Instruction index (from "0: addi x1 x2 10")
    mnemonic: str  # Instruction mnemonic (e.g., "addi", "add", "lw")
    operands: List[str]  # Raw operands as strings

    # Parsed operands (None if not applicable)
    rd: Optional[int] = None  # Destination register
    rs1: Optional[int] = None  # Source register 1
    rs2: Optional[int] = None  # Source register 2
    imm: Optional[int] = None  # Immediate value
    shamt: Optional[int] = None  # Shift amount

    raw_line: str = ""  # Original instruction line
    is_valid: bool = True  # Whether parsing was successful

    def to_dict(self) -> Dict[str, Any]:
        """Convert to dictionary."""
        return {
            "index": self.index,
            "mnemonic": self.mnemonic,
            "operands": self.operands,
            "rd": self.rd,
            "rs1": self.rs1,
            "rs2": self.rs2,
            "imm": self.imm,
            "shamt": self.shamt,
            "raw_line": self.raw_line,
            "is_valid": self.is_valid
        }


class AssemblyParser:
    """
    Parser for RISC-V assembly instructions.

    Handles various instruction formats:
    - I-type: addi rd rs1 imm
    - R-type: add rd rs1 rs2
    - S-type: sw rs2 offset(rs1)
    - B-type: beq rs1 rs2 offset
    - Shift: slli rd rs1 shamt
    - U-type: lui rd imm
    """

    # Instruction format patterns
    # Format: "index: mnemonic operands"
    INSTRUCTION_PATTERN = r'^(\d+):\s+(\w+)\s+(.*)$'

    # Register extraction: x0-x31
    REGISTER_PATTERN = r'x(\d+)'

    # Memory operand: offset(base)
    MEMORY_PATTERN = r'(-?\d+)\(x(\d+)\)'

    # Known instruction types
    I_TYPE_IMM = {'addi', 'addw', 'slti', 'sltiu', 'andi', 'ori', 'xori'}
    I_TYPE_LOAD = {'lw', 'ld', 'lb', 'lh', 'lbu', 'lhu', 'lwu'}
    R_TYPE = {'add', 'addw', 'sub', 'subw', 'and', 'or', 'xor',
              'slt', 'sltu', 'sll', 'srl', 'sra', 'sllw', 'srlw', 'sraw'}
    S_TYPE = {'sw', 'sd', 'sb', 'sh'}
    B_TYPE = {'beq', 'bne', 'blt', 'bge', 'bltu', 'bgeu'}
    SHIFT_IMM = {'slli', 'srli', 'srai', 'slliw', 'srliw', 'sraiw'}
    U_TYPE = {'lui', 'auipc'}
    J_TYPE = {'jal', 'jalr'}

    def __init__(self):
        """Initialize the parser."""
        self.instructions: List[ParsedInstruction] = []

    def parse(self, assembly_text: str) -> List[ParsedInstruction]:
        """
        Parse assembly text into structured instructions.

        Args:
            assembly_text: Multi-line assembly text

        Returns:
            List of ParsedInstruction objects
        """
        self.instructions = []

        if not assembly_text or not assembly_text.strip():
            return self.instructions

        for line in assembly_text.strip().split('\n'):
            line = line.strip()
            if not line:
                continue

            parsed = self._parse_line(line)
            if parsed:
                self.instructions.append(parsed)

        return self.instructions

    def _parse_line(self, line: str) -> Optional[ParsedInstruction]:
        """
        Parse a single instruction line.

        Args:
            line: Single instruction line (e.g., "0: addi x1 x2 10")

        Returns:
            ParsedInstruction or None if parsing failed
        """
        # Match basic instruction format
        match = re.match(self.INSTRUCTION_PATTERN, line)
        if not match:
            return None

        index = int(match.group(1))
        mnemonic = match.group(2).lower()
        operands_str = match.group(3).strip()

        # Split operands by spaces or commas
        operands = [op.strip() for op in re.split(r'[,\s]+', operands_str) if op.strip()]

        # Create instruction object
        instr = ParsedInstruction(
            index=index,
            mnemonic=mnemonic,
            operands=operands,
            raw_line=line
        )

        # Parse operands based on instruction type
        try:
            self._parse_operands(instr)
        except Exception as e:
            instr.is_valid = False
            # print(f"⚠️  Failed to parse operands for: {line} ({e})")

        return instr

    def _parse_operands(self, instr: ParsedInstruction):
        """Parse operands based on instruction type."""
        mnemonic = instr.mnemonic
        operands = instr.operands

        if mnemonic in self.I_TYPE_IMM:
            # Format: addi rd rs1 imm
            instr.rd = self._extract_register(operands[0])
            instr.rs1 = self._extract_register(operands[1])
            instr.imm = self._extract_immediate(operands[2])

        elif mnemonic in self.I_TYPE_LOAD:
            # Format: lw rd offset(rs1)
            instr.rd = self._extract_register(operands[0])
            if '(' in operands[1]:
                offset, base = self._extract_memory_operand(operands[1])
                instr.rs1 = base
                instr.imm = offset
            else:
                # Alternative format: lw rd rs1 offset
                instr.rs1 = self._extract_register(operands[1])
                if len(operands) > 2:
                    instr.imm = self._extract_immediate(operands[2])

        elif mnemonic in self.R_TYPE:
            # Format: add rd rs1 rs2
            instr.rd = self._extract_register(operands[0])
            instr.rs1 = self._extract_register(operands[1])
            instr.rs2 = self._extract_register(operands[2])

        elif mnemonic in self.S_TYPE:
            # Format: sw rs2 offset(rs1)
            instr.rs2 = self._extract_register(operands[0])
            if '(' in operands[1]:
                offset, base = self._extract_memory_operand(operands[1])
                instr.rs1 = base
                instr.imm = offset
            else:
                # Alternative format: sw rs2 rs1 offset
                instr.rs1 = self._extract_register(operands[1])
                if len(operands) > 2:
                    instr.imm = self._extract_immediate(operands[2])

        elif mnemonic in self.B_TYPE:
            # Format: beq rs1 rs2 offset
            instr.rs1 = self._extract_register(operands[0])
            instr.rs2 = self._extract_register(operands[1])
            instr.imm = self._extract_immediate(operands[2])

        elif mnemonic in self.SHIFT_IMM:
            # Format: slli rd rs1 shamt
            instr.rd = self._extract_register(operands[0])
            instr.rs1 = self._extract_register(operands[1])
            instr.shamt = self._extract_immediate(operands[2])
            instr.imm = instr.shamt  # For convenience

        elif mnemonic in self.U_TYPE:
            # Format: lui rd imm
            instr.rd = self._extract_register(operands[0])
            instr.imm = self._extract_immediate(operands[1])

        elif mnemonic in self.J_TYPE:
            # Format: jal rd offset or jalr rd rs1 offset
            instr.rd = self._extract_register(operands[0])
            if mnemonic == 'jalr' and len(operands) >= 2:
                instr.rs1 = self._extract_register(operands[1])
                if len(operands) > 2:
                    instr.imm = self._extract_immediate(operands[2])
            else:
                instr.imm = self._extract_immediate(operands[1])

    def _extract_register(self, operand: str) -> Optional[int]:
        """Extract register number from operand (e.g., 'x1' -> 1)."""
        match = re.search(self.REGISTER_PATTERN, operand)
        if match:
            return int(match.group(1))
        return None

    def _extract_immediate(self, operand: str) -> Optional[int]:
        """Extract immediate value from operand."""
        try:
            # Handle hex (0x...) and decimal
            operand = operand.strip()
            if operand.startswith('0x') or operand.startswith('0X'):
                return int(operand, 16)
            else:
                return int(operand)
        except ValueError:
            return None

    def _extract_memory_operand(self, operand: str) -> tuple[Optional[int], Optional[int]]:
        """
        Extract offset and base register from memory operand.

        Args:
            operand: Memory operand (e.g., "100(x2)")

        Returns:
            Tuple of (offset, base_register)
        """
        match = re.match(self.MEMORY_PATTERN, operand)
        if match:
            offset = int(match.group(1))
            base = int(match.group(2))
            return offset, base
        return None, None

    def get_instruction_count(self) -> int:
        """Get total number of parsed instructions."""
        return len(self.instructions)

    def get_valid_instruction_count(self) -> int:
        """Get number of successfully parsed instructions."""
        return sum(1 for instr in self.instructions if instr.is_valid)

    def get_mnemonics(self) -> List[str]:
        """Get list of all instruction mnemonics."""
        return [instr.mnemonic for instr in self.instructions]

    def get_instructions_by_mnemonic(self, mnemonic: str) -> List[ParsedInstruction]:
        """Get all instructions with a specific mnemonic."""
        return [instr for instr in self.instructions
                if instr.mnemonic.lower() == mnemonic.lower()]


def parse_assembly(assembly_text: str) -> List[ParsedInstruction]:
    """
    Convenience function to parse assembly text.

    Args:
        assembly_text: Multi-line assembly text

    Returns:
        List of ParsedInstruction objects
    """
    parser = AssemblyParser()
    return parser.parse(assembly_text)


# Example usage and testing
if __name__ == "__main__":
    # Test cases
    test_assembly = """
0: addi x1 x2 10
1: add x3 x4 x5
2: lw x6 100(x7)
3: sw x8 200(x9)
4: beq x10 x11 50
5: slli x12 x13 5
6: lui x14 0x12345
"""

    print("Testing AssemblyParser...")
    parser = AssemblyParser()
    instructions = parser.parse(test_assembly)

    print(f"\nParsed {len(instructions)} instructions:\n")
    for instr in instructions:
        print(f"{instr.index}: {instr.mnemonic:6s} ", end="")
        if instr.rd is not None:
            print(f"rd=x{instr.rd} ", end="")
        if instr.rs1 is not None:
            print(f"rs1=x{instr.rs1} ", end="")
        if instr.rs2 is not None:
            print(f"rs2=x{instr.rs2} ", end="")
        if instr.imm is not None:
            print(f"imm={instr.imm} ", end="")
        if instr.shamt is not None:
            print(f"shamt={instr.shamt} ", end="")
        print()

    print(f"\nValid instructions: {parser.get_valid_instruction_count()}/{parser.get_instruction_count()}")
    print(f"Mnemonics: {parser.get_mnemonics()}")
