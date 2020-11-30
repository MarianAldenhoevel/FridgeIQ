import sys

with open("C:\\Users\\Marian Aldenhövel\\Desktop\\FridgeIQ\\src\\blocking clauses\\FridgeIQGenerator.log") as fin:
    for line in fin:
        if not line.startswith("2019"):
            sys.stdout.write(line)