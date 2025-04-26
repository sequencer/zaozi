import argparse
from z3 import *
import re
from string import Template

def solve_and_replace(file_path):
    with open(file_path, 'r') as f:
        content = f.read()

    # Split the content into two parts: before and after "========="
    parts = content.split('====================')
    if len(parts) != 2:
        raise ValueError("File format is incorrect. Missing '====================' separator.")

    before, after = parts
    smtlib_expr = after.strip()

    # Parse the SMT-LIB expression using Z3
    solver = Solver()
    solver.from_string(smtlib_expr)

    # Check satisfiability and get the model
    if solver.check() == sat:
        model = solver.model()
        # Extract the values of all declared constants
        assignments = {str(d): model[d] for d in model.decls()}
    else:
        # If unsatisfiable, set all variables to default value 0
        assignments = {}

    # Use a string template to replace placeholders
    template = Template(before)
    # Replace variables with their solved values or default to 0
    resolved_before = template.safe_substitute(assignments)
    # Replace any unresolved placeholders with 0
    resolved_before = re.sub(r'x\$\w+', '0', resolved_before)

    print(resolved_before)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Solve SMT-LIB expressions and replace placeholders.")
    parser.add_argument("-f", "--file", required=True, help="Path to the SMT-LIB file.")
    args = parser.parse_args()

    solve_and_replace(args.file)