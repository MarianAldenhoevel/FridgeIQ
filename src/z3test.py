import z3

filename = 'z3test.smt'

# Make a solver with some arbitrary useless constraint
solver = z3.Solver()
solver.add(True)

# Save to file
smt2 = solver.sexpr()
with open(filename, mode='w', encoding='ascii') as f: # overwrite
    f.write(smt2)
    f.close()

# Load from file
filename = 'C:\\Users\\Marian Aldenhövel\\Desktop\\FridgeIQ\\src\\generate_all\\state.smt'

solver.reset()
solver.from_file(filename)

print(solver)