#!/usr/bin/env python3
"""
Documentation extraction pipeline for RVConstraints.scala.
Parses Scala source and extracts constraint function metadata.
"""

import re
from typing import List, Dict, Optional
from dataclasses import dataclass, asdict
from pathlib import Path

from config import SCALA_SOURCE_PATH, CATEGORIES


@dataclass
class ConstraintFunction:
    """Represents a constraint function from RVConstraints.scala."""
    function_name: str
    category: str
    subcategory: Optional[str]
    signature: str
    parameters: List[Dict[str, str]]
    return_type: str
    implementation: str
    description: str
    example_usage: str
    related_functions: List[str]
    source_line: int

    def to_dict(self) -> Dict:
        return asdict(self)

    def to_content(self) -> str:
        """Generate full text content for embedding."""
        content = f"{self.function_name}\n"
        content += f"Category: {self.category}\n"
        content += f"Description: {self.description}\n"
        content += f"Signature: {self.signature}\n"
        content += f"Example:\n{self.example_usage}\n"
        return content


class RVConstraintsParser:
    """Parser for RVConstraints.scala."""

    def __init__(self, file_path: Path):
        self.file_path = file_path
        self.lines = []
        self.functions = []

    def parse(self) -> List[ConstraintFunction]:
        """Parse file and extract all constraint functions."""

        with open(self.file_path, 'r', encoding='utf-8') as f:
            self.lines = f.readlines()

        # Parse each category
        self.functions.extend(self._parse_range_functions())
        self.functions.extend(self._parse_has_functions())
        self.functions.extend(self._parse_isa_functions())
        self.functions.extend(self._parse_instruction_functions())

        print(f"✅ Extracted {len(self.functions)} constraint functions")
        print(f"   - Range: {len([f for f in self.functions if f.category == 'range'])}")
        print(f"   - Has: {len([f for f in self.functions if f.category == 'has'])}")
        print(f"   - ISA Extension: {len([f for f in self.functions if f.category == 'isa_extension'])}")
        print(f"   - Instruction: {len([f for f in self.functions if f.category == 'instruction'])}")

        return self.functions

    def _parse_range_functions(self) -> List[ConstraintFunction]:
        """Parse range constraint functions like rdRange, rs1Range, etc."""

        functions = []
        pattern = r'def (\w+Range)\(start: Int, end: Int\)\(using [^)]+\): ArgConstraint = ArgConstraint\(summon\[Index\]\.(\w+) [^)]+\)'

        for line_num, line in enumerate(self.lines, 1):
            match = re.search(pattern, line)
            if match:
                func_name = match.group(1)
                field_name = match.group(2)

                func = ConstraintFunction(
                    function_name=func_name,
                    category="range",
                    subcategory=None,
                    signature=line.strip(),
                    parameters=[
                        {"name": "start", "type": "Int"},
                        {"name": "end", "type": "Int"}
                    ],
                    return_type="ArgConstraint",
                    implementation=match.group(0),
                    description=self._generate_range_description(func_name, field_name),
                    example_usage=self._generate_range_example(func_name),
                    related_functions=[f"has{field_name.capitalize()}"],
                    source_line=line_num
                )
                functions.append(func)

        return functions

    def _parse_has_functions(self) -> List[ConstraintFunction]:
        """Parse has* functions like hasRd, hasImm12, etc."""

        functions = []
        pattern = r'def (has\w+)\(\)\(using [^)]+\): ArgConstraint = (\w+Range)\((-?\d+), (-?\d+)\)'

        for line_num, line in enumerate(self.lines, 1):
            match = re.search(pattern, line)
            if match:
                func_name = match.group(1)
                delegates_to = match.group(2)
                min_val = match.group(3)
                max_val = match.group(4)

                func = ConstraintFunction(
                    function_name=func_name,
                    category="has",
                    subcategory=None,
                    signature=line.strip(),
                    parameters=[],
                    return_type="ArgConstraint",
                    implementation=f"{delegates_to}({min_val}, {max_val})",
                    description=self._generate_has_description(func_name),
                    example_usage=self._generate_has_example(func_name),
                    related_functions=[delegates_to],
                    source_line=line_num
                )
                functions.append(func)

        return functions

    def _parse_isa_functions(self) -> List[ConstraintFunction]:
        """Parse ISA extension functions like isRV64I, isRV32C, etc."""

        functions = []
        pattern = r'def (isRV\w+)\(\)\(using Recipe\): SetConstraint = SetConstraint\(summon\[Recipe\]\.(\w+)\)'

        for line_num, line in enumerate(self.lines, 1):
            match = re.search(pattern, line)
            if match:
                func_name = match.group(1)
                extension = match.group(2)

                func = ConstraintFunction(
                    function_name=func_name,
                    category="isa_extension",
                    subcategory=self._extract_isa_family(func_name),
                    signature=line.strip(),
                    parameters=[],
                    return_type="SetConstraint",
                    implementation=f"SetConstraint(summon[Recipe].{extension})",
                    description=self._generate_isa_description(func_name),
                    example_usage=self._generate_isa_example(func_name),
                    related_functions=[],
                    source_line=line_num
                )
                functions.append(func)

        return functions

    def _parse_instruction_functions(self) -> List[ConstraintFunction]:
        """Parse instruction constraint functions like isAddi, isSlli, etc."""

        functions = []
        # Pattern handles both simple and complex ISA requirements
        pattern = r'def (is[A-Z]\w+)\(\)\(using [^)]+\): InstConstraint = InstConstraint\(nameId\((\d+)\) & (.*?)\)$'

        for line_num, line in enumerate(self.lines, 1):
            match = re.search(pattern, line)
            if match:
                func_name = match.group(1)
                name_id = match.group(2)
                isa_constraint = match.group(3)

                # Extract ISA extension(s)
                isa_extensions = re.findall(r'isRV\w+\(\)', isa_constraint)

                func = ConstraintFunction(
                    function_name=func_name,
                    category="instruction",
                    subcategory=isa_extensions[0].replace("()", "") if isa_extensions else None,
                    signature=line.strip(),
                    parameters=[],
                    return_type="InstConstraint",
                    implementation=f"nameId({name_id}) & {isa_constraint}",
                    description=self._generate_instruction_description(func_name, isa_extensions),
                    example_usage=self._generate_instruction_example(func_name),
                    related_functions=self._find_related_fields(func_name),
                    source_line=line_num
                )
                functions.append(func)

        return functions

    # Description generators
    def _generate_range_description(self, func_name: str, field_name: str) -> str:
        field = field_name.replace("Range", "")
        descriptions = {
            "rd": "destination register (目标寄存器)",
            "rs1": "source register 1 (源寄存器1)",
            "rs2": "source register 2 (源寄存器2)",
            "rs3": "source register 3 (源寄存器3)",
            "imm12": "12-bit immediate value (12位立即数)",
            "imm20": "20-bit immediate value (20位立即数)",
            "shamtw": "shift amount (移位量)",
        }
        field_desc = descriptions.get(field, field)
        return f"Constrains the {field_desc} to a range [start, end). Common for specifying register or immediate value bounds."

    def _generate_has_description(self, func_name: str) -> str:
        field = func_name.replace("has", "").lower()
        return f"Checks if the instruction uses the {field} field. Useful for filtering instruction types."

    def _generate_isa_description(self, func_name: str) -> str:
        ext = func_name.replace("is", "")
        return f"Selects the {ext} instruction set extension. Use this in the 'sets' declaration or instruction constraints."

    def _generate_instruction_description(self, func_name: str, isa_exts: List[str]) -> str:
        inst_name = func_name.replace("is", "").upper()
        ext_str = ", ".join([e.replace("is", "").replace("()", "") for e in isa_exts]) if isa_exts else "multiple"
        return f"Constrains instruction to be {inst_name} (part of {ext_str}). Use as opcode constraint in instruction() blocks."

    # Example generators
    def _generate_range_example(self, func_name: str) -> str:
        return f"""instruction(0, isAddi()) {{
  {func_name}(1, 16) & rs1Range(1, 32)
}}"""

    def _generate_has_example(self, func_name: str) -> str:
        return f"""// Check if instruction has this field
instruction(0, someOpcode()) {{
  {func_name}()
}}"""

    def _generate_isa_example(self, func_name: str) -> str:
        return f"""object test extends RVGenerator:
  val sets = {func_name}()
  def constraints() = ...
"""

    def _generate_instruction_example(self, func_name: str) -> str:
        inst_name = func_name.replace("is", "")
        # Infer common fields - include ALL fields with proper range values
        fields = self._find_related_fields(func_name)
        if fields:
            parts = []
            for f in fields:
                if f.startswith("imm12") or f.startswith("bimm12"):
                    parts.append(f"{f}Range(-2048, 2047)")
                elif f.startswith("imm20"):
                    parts.append(f"{f}Range(0, 1048576)")
                elif f.startswith("shamtw"):
                    parts.append(f"{f}Range(0, 32)")
                elif f.startswith("shamtd"):
                    parts.append(f"{f}Range(0, 64)")
                else:
                    parts.append(f"{f}Range(1, 32)")
            field_constraints = " & ".join(parts)
        else:
            field_constraints = "/* argument constraints */"

        return f"""instruction(0, {func_name}()) {{
  {field_constraints}
}}"""

    def _find_related_fields(self, func_name: str) -> List[str]:
        """Infer common register/immediate fields for an instruction."""
        inst = func_name.lower()

        # Exact matches first (order matters: check more specific patterns before general ones)
        # RV64I word-width shift instructions use shamtw
        if "slliw" in inst or "srliw" in inst or "sraiw" in inst:
            return ["rd", "rs1", "shamtw"]
        # RV64I shift instructions use shamtd (6-bit shift amount for 64-bit)
        elif "sllirv64i" in inst or "srlirv64i" in inst or "srairv64i" in inst:
            return ["rd", "rs1", "shamtd"]
        # RV32I shift instructions use shamtw (5-bit shift amount for 32-bit)
        elif "sllirv32i" in inst or "srlirv32i" in inst or "srairv32i" in inst:
            return ["rd", "rs1", "shamtw"]
        # Generic shift (fallback to shamtw)
        elif "slli" in inst or "srli" in inst or "srai" in inst:
            return ["rd", "rs1", "shamtw"]
        # Immediate arithmetic
        elif "addi" in inst or "andi" in inst or "ori" in inst or "xori" in inst or "slti" in inst:
            return ["rd", "rs1", "imm12"]
        # Register-register arithmetic and logic
        elif "add" in inst or "sub" in inst or "and" in inst or "or" in inst or "xor" in inst or "slt" in inst or "sll" in inst or "srl" in inst or "sra" in inst:
            return ["rd", "rs1", "rs2"]
        # Branch instructions
        elif "beq" in inst or "bne" in inst or "blt" in inst or "bge" in inst:
            return ["rs1", "rs2", "bimm12hi", "bimm12lo"]
        # Load instructions
        elif "lw" in inst or "ld" in inst or "lb" in inst or "lh" in inst or "lbu" in inst or "lhu" in inst or "lwu" in inst:
            return ["rd", "rs1", "imm12"]
        # Store instructions
        elif "sw" in inst or "sd" in inst or "sb" in inst or "sh" in inst:
            return ["rs1", "rs2", "imm12hi", "imm12lo"]
        # LUI/AUIPC
        elif "lui" in inst or "auipc" in inst:
            return ["rd", "imm20"]
        # JAL
        elif "jal" in inst and "jalr" not in inst:
            return ["rd", "jimm20"]
        # JALR
        elif "jalr" in inst:
            return ["rd", "rs1", "imm12"]
        else:
            return ["rd", "rs1"]  # Default

    def _extract_isa_family(self, func_name: str) -> str:
        """Extract ISA family from function name, e.g., isRV64I -> RV64I."""
        return func_name.replace("is", "")


def main():
    """Run extraction pipeline."""
    parser = RVConstraintsParser(SCALA_SOURCE_PATH)
    functions = parser.parse()

    # Return for use by indexer
    return functions


if __name__ == "__main__":
    main()
