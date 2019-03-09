import z3

solver = z3.Solver()

xs = [ z3.Bool("x_{i}".format(i=i)) for i in range(0,10) ]
ys = [ z3.Bool("y_{i}".format(i=i)) for i in range(0,10) ]

solver.add(z3.Or(xs) == z3.Or(ys))

#solver.add(any(xs) == any(ys))

#xsum = z3.Sum([z3.If(x,1,0) for x in xs])
#ysum = z3.Sum([z3.If(x,1,0) for x in ys])
#solver.add(xsum == ysum)

solver.check()
print(solver.model())