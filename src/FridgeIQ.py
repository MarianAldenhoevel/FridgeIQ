# -*- coding: utf-8 -*-
'''
@author: Marian Aldenhövel
'''

import math
import logging
import os
import sys
import time
import copy

from operator import attrgetter
from matplotlib import pyplot as plt
from shapely.geometry.polygon import Polygon
from shapely.geometry.point import Point
from shapely.ops import cascaded_union
from shapely.affinity import translate
from shapely.affinity import rotate
from descartes import PolygonPatch

import math

runfolder = os.path.dirname(os.path.realpath(__file__)) + '\\' + time.strftime('%Y-%m-%d-%H-%M-%S', time.localtime())
os.makedirs(runfolder)

class Part:

  def __init__(self, name, polygon, color):
      self.name = name
      self.polygon = polygon
      self.color = color
      self.xoffset = 0
      self.yoffset = 0
      self.rotation = 0
      
class BoardState:

  framenr = 0
  logger = logging.getLogger('Board')
  
  def __init__(self, target, parts_placed, parts_available):
      self.target = target
      self.parts_placed = parts_placed
      self.parts_available = parts_available

  def plot(self, caption = '', movingpart = None, candidatepositions = None):
    fig = plt.figure(1, figsize=(5,5), dpi=90)
    ax = fig.add_subplot(1,1,1) # rows, columns, index

    i = 0
    xoffset = 0
    yoffset = 0
    extents = Point(0,0)

    # plot the target polygon
    patch = PolygonPatch(self.target, facecolor='#cccccc')
    ax.add_patch(patch)
    extents = extents.union(target)

    # plot the placed parts on top of the target
    for part in self.parts_placed:
        polygon = translate(rotate(part.polygon, part.rotation), part.xoffset, part.yoffset)
        extents = extents.union(polygon)
        patch = PolygonPatch(polygon, facecolor=part.color)
        ax.add_patch(patch)

    # plot the available parts off to the side
    bounds = target.bounds
    xoffset = bounds[0] # minx
    yoffset = bounds[1]-4 # miny and down from there
    for part in self.parts_available:
        polygon = translate(part.polygon, xoffset, yoffset)
        extents = extents.union(polygon)
        patch = PolygonPatch(polygon, facecolor=part.color)
        ax.add_patch(patch)
        xoffset = xoffset + 4
        if xoffset > 12:
            xoffset = 0
            yoffset = yoffset - 4

    # plot the part that is on the move
    if movingpart:
        self.logger.debug('movingpart xoffset={xoffset}, yoffset={yoffset}, rotation={rotation}'.format(xoffset=movingpart.xoffset, yoffset=movingpart.yoffset, rotation=movingpart.rotation))
        polygon = translate(rotate(movingpart.polygon, movingpart.rotation), movingpart.xoffset, movingpart.yoffset)
        extents = extents.union(polygon)
        patch = PolygonPatch(polygon, facecolor=movingpart.color, alpha=0.5)
        ax.add_patch(patch)

    # plot candidatepositions
    if candidatepositions:
      for part in candidatepositions:
        polygon = translate(rotate(part.polygon, part.rotation), part.xoffset, part.yoffset)
        extents = extents.union(polygon)
        patch = PolygonPatch(polygon, facecolor=part.color, alpha=0.2)
        ax.add_patch(patch)

    bounds = extents.bounds

    ax.set_title('FridgeIQ')
    xrange = [bounds[0]-1, bounds[2]+1]
    yrange = [bounds[1]-1, bounds[3]+1]
    ax.set_xlim(*xrange)
    ax.set_ylim(*yrange)
    ax.set_aspect(1)
    global fignr
    global runfolder
    figname = runfolder + '\\{n:05d}'.format(n=BoardState.framenr)
    if caption:
      figname += '_' + caption
    figname += '.png'
    fig.savefig(figname)
    plt.close(fig)
    BoardState.framenr += 1

def solve(board):

  indent = "  " * len(board.parts_placed)
    
  if not board.parts_available:
    # No more parts to place. We are done.
    logger.debug(indent + 'Solved')
    board.plot('solution')
  else:
    # Pick the largest part left. The list is sorted in descending order.
    #
    # Generate all possible legal positions this part can go in. This is
    # done in a discrete fashion by scanning the bounding box of the candidate
    # part in steps over the bounds of the target and checking the conditions.
    # The scanning happens in steps and is repeated for each possible 45 degree
    # rotation.
    nextpart = board.parts_available[0]
    
    targetbounds = target.bounds
    #logger.debug(indent + 'targetbounds={targetbounds}'.format(targetbounds=targetbounds));
    targetwidth = targetbounds[2]-targetbounds[0]
    targetheight = targetbounds[3]-targetbounds[1]

    candidatepositions = [];
      
    for rotation in range(0, 360, 90):
      # Clone part in default position 
      part = copy.deepcopy(nextpart);

      # Rotate in place
      poly = rotate(part.polygon, rotation)
  
      # Figure out the part bounds in that orientation. This will not change
      # during the scan.
      partbounds = poly.bounds
      #logger.debug(indent + 'partbounds={partbounds}'.format(partbounds=partbounds));
      partwidth = partbounds[2]-partbounds[0]
      partheight = partbounds[3]-partbounds[1]
      
      # Initialize offsets so that the part is placed at the bottom-left
      # corner of the target.
      initialxoffset = targetbounds[0]-partbounds[0]
      initialyoffset = targetbounds[1]-partbounds[1]
      
      # scan over the width and height of the target bounds.
      xoffset = 0
      while xoffset + partwidth <= targetwidth:
        yoffset = 0
        while yoffset + partheight <= targetheight:
          #logger.debug(indent + 'trying xoffset={xoffset}, yoffset={yoffset}, rotation={rotation}'.format(xoffset=xoffset, yoffset=yoffset, rotation=rotation))
          
          part.rotation = rotation
          part.xoffset = initialxoffset + xoffset
          part.yoffset = initialyoffset + yoffset

          # What about this position? Remember the poly is already rotated.
          testpoly = translate(poly, part.xoffset, part.yoffset)

          # Conditions:
          # The candidate part has to be completely inside the target
          # The candidate part may not overlap any of the that already have been placed.

          if target.contains(testpoly):
            #logger.debug(indent + 'part is inside target')
            overlaps = False
            for part_placed in board.parts_placed:
              poly_placed = translate(rotate(part_placed.polygon, part_placed.rotation), part_placed.xoffset, part_placed.yoffset)
              if poly_placed.intersects(testpoly):
                #logger.debug(indent + 'part overlaps with already placed part {name}'.format(name=part_placed.name))
                overlaps = True
            if not overlaps:
              #logger.debug(indent + 'no overlap, good placement!')              
              candidatepositions.append(copy.deepcopy(part))              
          #else:
            #logger.debug(indent + 'part sticks out from target')
          
          yoffset = yoffset + 1
        xoffset = xoffset + 1

    if len(candidatepositions) == 0:
      logger.debug(indent + 'Found no candidate positions for part {name}. Dead end'.format(n=len(candidatepositions), name=part.name))
      board.plot('deadend')
    else:      
      logger.debug(indent + 'Found {n} candidate positions for part {name}'.format(n=len(candidatepositions), name=part.name))
      board.plot('candidates', None, candidatepositions)

      # try each candidate position
      i = 1
      for candidate in candidatepositions:
        logger.debug(indent + 'Try candidate position #{i}'.format(i=i))
        next_board = copy.deepcopy(board)
        next_board.parts_available.pop(0)
        next_board.parts_placed.append(candidate)
        next_board.plot('try{i:02d}'.format(i=i), candidate)
        solve(next_board)
        i += 1

# set up logging
fh = logging.FileHandler(runfolder + '\\FridgeIQ.log')
fh.setLevel(logging.DEBUG)

ch = logging.StreamHandler()
ch.setLevel(logging.DEBUG)

ch.setFormatter(logging.Formatter('({thread}) {name} [{levelname}:7}] - {message}', style='{'))
ch.setFormatter(logging.Formatter('{asctime} ({thread}) {name} [{levelname:7}] - {message}', style='{'))

root = logging.getLogger()
root.addHandler(ch)
root.addHandler(fh)
root.setLevel(logging.DEBUG)

logging.getLogger('matplotlib').setLevel(logging.INFO)

logger = logging.getLogger('Main')
logger.info('starting')

colors = ['red', 'green', 'blue', 'purple', 'yellow']
    
# Create a dictionary for all the parts that make up the puzzle.
partscatalog = {
    'A' : Part('A', Polygon([(0, 0), (1, 0), (1, 1), (2, 1), (1, 2), (0, 2), (0, 0)]), 'red'),
    'R' : Part('R', Polygon([(1, 0), (2, 0), (2, 2), (1, 2), (0, 1), (1, 1), (1, 0)]), 'green'),
    'E' : Part('E', Polygon([(1, 0), (2, 0), (2, 2), (1, 2), (0, 1), (1, 1), (1, 0)]), 'blue'),
    'L' : Part('L', Polygon([(0, 0), (2, 0), (2, 1), (3, 1), (2, 2), (1, 2), (1, 1), (0, 1), (0, 0)]), 'purple'),
    'O' : Part('O', Polygon([(0, 0), (2, 0), (1, 1), (1, 2), (0, 2), (0, 0)]), 'yellow'),
    'M' : Part('M', Polygon([(0, 0), (1, 0), (1, 2), (0, 1), (0, 0)]), 'red'),
    'T' : Part('T', Polygon([(0, 0), (3, 0), (1, 2), (1, 1), (0, 1), (0, 0)]), 'green',),
    'S' : Part('S', Polygon([(0, 0), (1, 0), (1, 3), (0, 2), (0, 0)]), 'blue'),
    'Q' : Part('Q', Polygon([(0, 0), (1, 0), (1, 2), (0, 2), (0, 0)]), 'purple'),
    'D' : Part('D', Polygon([(0, 0), (2, 0), (1, 1), (0, 0)]), 'yellow'),
    'J' : Part('J', Polygon([(0, 0), (2, 0), (2, 2), (1, 2), (1, 1), (0, 1), (0, 0)]), 'red'),
    'B' : Part('B', Polygon([(0, 0), (2, 0), (2, 1), (0, 1), (0, 0)]), 'green'),
    'N' : Part('N', Polygon([(0, 0), (1, 0), (1, 1), (3, 1), (3, 2), (0, 2), (0, 0)]), 'blue'),
    'Y' : Part('Y', Polygon([(0, 0), (1, 0), (1, 1), (0, 2), (0, 0)]), 'purple'),
    'I' : Part('I', Polygon([(0, 0), (2, 0), (2, 2), (0, 0)]), 'yellow'),
    'U' : Part('U', Polygon([(1, 0), (2, 0), (2, 2), (1, 2), (1, 3), (0, 3), (0, 1), (1, 1), (1, 0)]), 'red')
}

# A list of all the parts available. This is actually a string, but we make it
# from the catalog keys so we don't forget anyone.
allparts = ''.join(partscatalog.keys())

# Set up the default puzzles. Each as a string and we can make a list of parts for
# them from the catalog if we want.
puzzle_square_1  = 'IJMR'
puzzle_square_2  = 'BDJNQSY'
puzzle_square_3  = 'ADJMNSY'
puzzle_square_4  = 'AIJMOQS'
puzzle_square_5  = 'ABDEIMNYRST'
puzzle_square_6  = 'ABDMNOQRSTY'
puzzle_square_7  = 'ABDEIJMNOSY'
puzzle_square_8  = 'ABIJMOQRSTY'
puzzle_square_9  = 'ARELOMSQJBNYIU'
puzzle_square_10 = 'ARELOMTSQDJBNYI'

# Helper function to create a square of given side-length as a target shape.
def target_square(sides):
  return Polygon([(0, 0), (sides, 0), (sides, sides), (0, sides), (0, 0)])

# Helper function to create a more interesting target shape.
def target_octagon():
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

# Make a list of parts for the puzzle. Sort by descending area.
parts = [p for p in partscatalog.values() if p.name in list(puzzle)]
parts.sort(key=lambda part: (part.polygon.area, part.name), reverse=True) 

# Plot some information about the puzzle initial state
logger.debug('Target area={area}'.format(area=target.area))
logger.debug('Parts available in descending order of area:')
totalarea = 0
for part in parts:
  logger.debug('{name}: area={area}'.format(name=part.name, area=part.polygon.area))
  totalarea += part.polygon.area
logger.debug('Total area of parts={totalarea}'.format(totalarea=totalarea))
if totalarea == target.area:
  logger.debug('Total parts area matches target area. A valid puzzle.')
else:
  raise ValueError('Total parts area does not match target area, puzzle is invalid.')

# Create the initial board state
board = BoardState(target, [], parts)

# Try to solve it
board.plot('setup')
solve(board)

#input('Press Enter to continue...')
