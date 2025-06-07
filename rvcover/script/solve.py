import argparse
from z3 import *
from string import Template

def parse_instruction_map(inst_path: str):
    with open(inst_path, 'r') as f:
        lines = f.readlines()

    inst_map = {}
    for idx, line in enumerate(lines):
        inst_map[idx] = [x.strip() for x in line.split(",")]

    return inst_map

def parse_arg_lut(argLut_path: str):
    with open(argLut_path, 'r') as f:
        lines = f.readlines()
    
    arg_lut = {}
    for idx, line in enumerate(lines):
        arg_lut[line.strip()] = idx
    
    return arg_lut

def parse_smtlib(file_path: str):
    # Parse the SMT-LIB expression using Z3
    solver = Solver()
    solver.from_file(file_path)

    solver.set(timeout=1000)

    solver.set("random_seed", 10)

    # Check satisfiability and get the model
    if solver.check() == sat:
        model = solver.model()
        # Extract the values of all declared constants
        return {str(d): model[d] for d in model.decls()}
    elif solver.check() == unsat:
        # If unsatisfiable, print the log and return
        print("The SMT-LIB file is unsat.")
        print(solver.unsat_core())
        return None
    else:
        print("The SMT-LIB file is unknown because of", solver.reason_unknown())
        return None
    

def parse_template(template_path: str):
    with open(template_path, 'r') as f:
        template = f.read()

    # Use a string template to replace placeholders
    template = Template(template)
    return template

def parse(inst_path: str, argLut_path: str, file_path: str, template_path: str):
    # Parse instruction map
    inst_map = parse_instruction_map(inst_path)

    # Parse argument lookup table
    arg_lut = parse_arg_lut(argLut_path)

    # Parse SMT-LIB file to get variable assignments
    assignments = parse_smtlib(file_path)

    # Parse template file
    template = parse_template(template_path)

    return inst_map, arg_lut, assignments, template

# Parse the resolved string to get instruction index and argument indices
# The resolved string is in the format: "idx, inst_idx, arg1, arg2, ..."
def parse_resolved(s: str):
    resolved = [x.strip() for x in s.split(",")]

    # Get the index of the instruction
    idx = resolved[0]

    # Get instruction and argument indices
    # For add instruction, the value of inst_idx is 0
    inst_idx = int(resolved[1])

    # Get all the arguments template, defined by arg_lut, including 'amoop', 'aq'...
    full_args = resolved[2:]

    return(idx, inst_idx, full_args)

def solve_and_replace(inst_path: str, argLut_path: str, file_path: str, template_path: str):
    inst_map, arg_lut_map, assignments, template = parse(inst_path, argLut_path, file_path, template_path)

    if assignments is None:
        return

    # Substitute assignments into template, get the third line and split by comma
    substituted = template.safe_substitute(assignments).split("\n")[2:]

    for line in substituted:
        idx, inst_idx, full_args = parse_resolved(line)

        # Get the instruction name and argument names from the instruction map
        instruction_name = inst_map[inst_idx][0]
        args_name = inst_map[inst_idx][1:]

        # Find the index of each argument name in the arg_lut map
        # For example, 'Rs1' would be mapped to 65 
        args_idx = [arg_lut_map[name] for name in args_name]

        # Get argument values in the full_args list, which is resolved from SMT-LIB
        args = [full_args[i] for i in args_idx]

        # Generate prefix for each argument, if the argument name starts with "R", prefix it with "x"
        # for example, if the argument name is "Rs1", the prefix will be "x", the value is "1", so the final value will be "x1"
        prefix = ["x" if name.startswith("R") else "" for name in args_name]

        # Combine prefix and argument value
        arg = " ".join([f"{p}{a}" for p, a in zip(prefix, args)])

        # Print final result
        print(f"{idx}: {instruction_name} {arg}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Solve SMT-LIB expressions and replace placeholders.")
    parser.add_argument("-i", "--inst", required=True, help="Path to the instruction map file.")
    parser.add_argument("-a", "--arg_lut", required=True, help="Path to the arg lut map file.")
    parser.add_argument("-f", "--file", required=True, help="Path to the SMT-LIB file.")
    parser.add_argument("-t", "--template", required=True, help="Path to the template file.")
    args = parser.parse_args()

    solve_and_replace(args.inst, args.arg_lut, args.file, args.template)
