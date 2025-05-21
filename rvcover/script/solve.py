import argparse
from z3 import *
import re
from string import Template

def solve_and_replace(file_path, template_path):
    with open(file_path, 'r') as f:
        content = f.read()

    with open(template_path, 'r') as f:
        template = f.read()

    # # Parse the SMT-LIB expression using Z3
    solver = Solver()
    solver.from_string(content)

    print("Parsed SMT-LIB expression:", content)

    # Check satisfiability and get the model
    if solver.check() == sat:
        model = solver.model()
        print(model.decls())
        # Extract the values of all declared constants
        assignments = {str(d): model[d] for d in model.decls()}
    else:
        # If unsatisfiable, print the log and return
        print("Unsatisfiable")
        return
    
    print("Assignments:", assignments)

    # Use a string template to replace placeholders
    template = Template(template)

    resolved = template.safe_substitute(assignments)

    resolved = re.sub(r"x-1 ", "", resolved)

    print(resolved)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Solve SMT-LIB expressions and replace placeholders.")
    parser.add_argument("-f", "--file", required=True, help="Path to the SMT-LIB file.")
    parser.add_argument("-t", "--template", required=True, help="Path to the template file.")
    args = parser.parse_args()

    solve_and_replace(args.file, args.template)