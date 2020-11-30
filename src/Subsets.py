import itertools

# Create a list of all parts by name
allparts = list('QBARELOMTSDJNYIU')

# Create all subsets from that list, ignore those of length 0, 1 and all and
# also those that differ only in the alternating use of parts B and Q which 
# are identical.

print("REM This is a generated file. See Subsets.py for how it is generated.") 
canonicalnames = {}
nn = 0
for r in range(2, len(allparts)):
    print("REM")
    print("REM -- Size {r}".format(r=r))
    n = 0
    for c in itertools.combinations(allparts, r):
        name = "".join(c)
        canonicalname = name.replace("B", "_").replace("Q", "_")
        if canonicalname not in canonicalnames:
            n += 1
            nn += 1
            foldername = "subset-{r:04d}-{n:04d}-{name}".format(r=r, n=n, name=name)
            cmd = "python .\\FridgeIQGenerator.py --log-level DEBUG --play-fanfare False --parts-list {name} --output-folder .\\{foldername} --save-state Solver-State.smt2".format(name=name, foldername=foldername)
            print(cmd)
            canonicalnames[canonicalname] = True
    print("REM -- Size {r} - Total {n}".format(r=r, n=n))
    
print("REM")
print("REM -- Total {nn}".format(nn=nn))
    