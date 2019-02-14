# -*- coding: utf-8 -*-
"""
@author: Marian Aldenhövel
"""

from matplotlib import pyplot as plt
from shapely.geometry.polygon import Polygon
from shapely.geometry.point import Point
from shapely.ops import cascaded_union
from shapely.affinity import translate
from descartes import PolygonPatch

# Create polygons for all the parts that make up the puzzle.
partscatalog = {
    "A" : Polygon([(0, 0), (1, 0), (1, 1), (2, 1), (1, 2), (0, 2), (0, 0)]),
    "R" : Polygon([(1, 0), (2, 0), (2, 2), (1, 2), (0, 1), (1, 1), (1, 0)]),
    "E" : Polygon([(1, 0), (2, 0), (2, 2), (1, 2), (0, 1), (1, 1), (1, 0)]),
    "L" : Polygon([(0, 0), (2, 0), (2, 1), (3, 1), (2, 2), (1, 2), (1, 1), (0, 1), (0, 0)]),
    "O" : Polygon([(0, 0), (2, 0), (1, 1), (1, 2), (0, 2), (0, 0)]),
    "M" : Polygon([(0, 0), (1, 0), (1, 2), (0, 1), (0, 0)]),
    "T" : Polygon([(0, 0), (3, 0), (1, 2), (1, 1), (0, 1), (0, 0)]),
    "S" : Polygon([(0, 0), (1, 0), (1, 3), (0, 2), (0, 0)]),
    "Q" : Polygon([(0, 0), (1, 0), (1, 2), (0, 2), (0, 0)]),
    "D" : Polygon([(0, 0), (2, 0), (1, 1), (0, 0)]),
    "J" : Polygon([(0, 0), (2, 0), (2, 2), (1, 2), (1, 1), (0, 1), (0, 0)]),
    "B" : Polygon([(0, 0), (2, 0), (2, 1), (0, 1), (0, 0)]),
    "N" : Polygon([(0, 0), (1, 0), (1, 1), (3, 1), (3, 2), (0, 2), (0, 0)]),
    "Y" : Polygon([(0, 0), (1, 0), (1, 1), (0, 2), (0, 0)]),
    "I" : Polygon([(0, 0), (2, 0), (2, 2), (0, 0)]),
    "U" : Polygon([(1, 0), (2, 0), (2, 2), (1, 2), (1, 3), (0, 3), (0, 1), (1, 1), (1, 0)])
}

allparts = ''.join(partscatalog.keys())

# Set up the default puzzles.
puzzle_square_1  = "IJMR"
puzzle_square_2  = "BDJNQSY"
puzzle_square_3  = "ADJMNSY"
puzzle_square_4  = "AIJMOQS"
puzzle_square_5  = "ABDEIMNYRST"
puzzle_square_6  = "ABDMNOQRSTY"
puzzle_square_7  = "ABDEIJMNOSY"
puzzle_square_8  = "ABIJMOQRSTY"
puzzle_square_9  = "ARELOMSQJBNYIU"
puzzle_square_10 = "ARELOMTSQDJBNYI"

def target_square(sides):
  return Polygon([(0, 0), (sides, 0), (sides, sides), (0, sides), (0, 0)])

def target_octagon():
    # Set up octagonal target shape
    m = 1
    n = 2.5*m
    a = 0
    b = a + m
    c = b + n + n
    d = c + m

    outer = Polygon([
        (b, a),
        (c, a),
        (c, b),
        (d, b),
        (d, c),
        (c, c),
        (c, d),
        (b, d),
        (b, c),
        (a, c),
        (a, b),
        (b, b),
        (b, a)
    ])

    inner = Polygon([
        (b+m, a+m),
        (c-m, a+m),
        (c-m, b+m),
        (d-m, b+m),
        (d-m, c-m),
        (c-m, c-m),
        (c-m, d-m),
        (b+m, d-m),
        (b+m, c-m),
        (a+m, c-m),
        (a+m, b+m),
        (b+m, b+m),
        (b+m, a+m) 
    ])

    octagon = Polygon([
        (3*m,   m),
        (d-3*m, m),
        (d-m,   3*m),
        (d-m,   d-3*m),
        (d-3*m, d-m),
        (3*m,   d-m),
        (m,     d-3*m),
        (m,     3*m),
        (3*m,   m)
    ])

    mid = m + n
    hole = 0.5
    inner_square = Polygon([
        (mid-hole, mid-hole),
        (mid+hole, mid-hole),
        (mid+hole, mid+hole),
        (mid-hole, mid+hole),
        (mid-hole, mid-hole)
    ])

    return outer.difference(inner).union(octagon.difference(inner_square))


# Select a puzzle to work on.
#puzzle = puzzle_square_1
#target = target_square(3)

#puzzle = puzzle_square_2
#target = target_square(4)

#puzzle = puzzle_square_3
#target = target_square(4)

#puzzle = puzzle_square_4
#target = target_square(4)

#puzzle = puzzle_square_5
#target = target_square(5)

#puzzle = puzzle_square_6
#target = target_square(5)

#puzzle = puzzle_square_7
#target = target_square(5)

#puzzle = puzzle_square_8
#target = target_square(5)

#puzzle = puzzle_square_9
#target = target_square(6)

#puzzle = puzzle_square_10
#target = target_square(6)

puzzle = allparts
target = target_octagon();

# What parts are available for this puzzle?
parts = { k: partscatalog[k] for k in list(puzzle) }

fig = plt.figure(1, figsize=(5,5), dpi=90)
ax = fig.add_subplot(1,1,1) # rows, columns, index

colors = ["red", "green", "blue", "purple", "yellow"]
i = 0
xoffset = 0
yoffset = 0
extents = Point(0,0)

for partname in parts:
    part = translate(parts[partname], xoffset, yoffset)

    print("Part {name}, area={area}".format(name=partname, area=part.area))

    extents = extents.union(part)
    patch = PolygonPatch(part, facecolor=colors[i])
    ax.add_patch(patch)
    i = (i + 1) % len(colors)
    xoffset = xoffset + 4
    if xoffset > 12:
        xoffset = 0
        yoffset = yoffset - 4

print("total parts area={0}".format(extents.area))

target = translate(target, 0, 4)
print("target area={0}".format(target.area))

patch = PolygonPatch(target, facecolor="black")
ax.add_patch(patch)
extents = extents.union(target)

bounds = extents.bounds
print("extents.bounds={0}".format(bounds))

ax.set_title('FridgeIQ')
xrange = [bounds[0]-1, bounds[2]+1]
yrange = [bounds[1]-1, bounds[3]+1]
ax.set_xlim(*xrange)
ax.set_ylim(*yrange)
ax.set_aspect(1)
fig.show()
#input("Press Enter to continue...")
