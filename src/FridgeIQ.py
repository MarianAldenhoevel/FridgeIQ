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
import simpleaudio

import matplotlib
matplotlib.use('agg') # select a non-interactive backend. Do this before importing pyplot!

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

plotcandidates = False
plotdeadends = False
plotsolutions = True
plotstepbystep = False
finalpositions = 0

class Part:
  
  def __init__(self, name, polygon, color):
      self.name = name
      self.polygon = polygon
      self.color = color
      self.xoffset = 0
      self.yoffset = 0
      self.rotation = 0
      self.candidateposition = []

      # build a list of distinct rotations
      self.rotations = [0]
      rotation_polys = [self.polygon]
      for rotation in range(90, 360, 90):
        test = rotate(self.polygon, rotation)
        if not any(test.equals(poly) for poly in rotation_polys):
          self.rotations.append(rotation)
          rotation_polys.append(test)
  
  def finalpolygon(self):
    return translate(rotate(self.polygon, self.rotation), self.xoffset, self.yoffset)

class Puzzle:
  # Create a list of all the parts that make up the puzzle.
  partscatalog = [
    Part('A', Polygon([(0, 0), (1, 0), (1, 1), (2, 1), (1, 2), (0, 2), (0, 0)]), 'red'),
    Part('R', Polygon([(1, 0), (2, 0), (2, 2), (1, 2), (0, 1), (1, 1), (1, 0)]), 'green'),
    Part('E', Polygon([(1, 0), (2, 0), (2, 2), (1, 2), (0, 1), (1, 1), (1, 0)]), 'blue'),
    Part('L', Polygon([(0, 0), (2, 0), (2, 1), (3, 1), (2, 2), (1, 2), (1, 1), (0, 1), (0, 0)]), 'purple'),
    Part('O', Polygon([(0, 0), (2, 0), (1, 1), (1, 2), (0, 2), (0, 0)]), 'yellow'),
    Part('M', Polygon([(0, 0), (1, 0), (1, 2), (0, 1), (0, 0)]), 'red'),
    Part('T', Polygon([(0, 0), (3, 0), (1, 2), (1, 1), (0, 1), (0, 0)]), 'green',),
    Part('S', Polygon([(0, 0), (1, 0), (1, 3), (0, 2), (0, 0)]), 'blue'),
    Part('Q', Polygon([(0, 0), (1, 0), (1, 2), (0, 2), (0, 0)]), 'purple'),
    Part('D', Polygon([(0, 0), (2, 0), (1, 1), (0, 0)]), 'yellow'),
    Part('J', Polygon([(0, 0), (2, 0), (2, 2), (1, 2), (1, 1), (0, 1), (0, 0)]), 'red'),
    Part('B', Polygon([(0, 0), (2, 0), (2, 1), (0, 1), (0, 0)]), 'green'),
    Part('N', Polygon([(0, 0), (1, 0), (1, 1), (3, 1), (3, 2), (0, 2), (0, 0)]), 'blue'),
    Part('Y', Polygon([(0, 0), (1, 0), (1, 1), (0, 2), (0, 0)]), 'purple'),
    Part('I', Polygon([(0, 0), (2, 0), (2, 2), (0, 0)]), 'yellow'),
    Part('U', Polygon([(1, 0), (2, 0), (2, 2), (1, 2), (1, 3), (0, 3), (0, 1), (1, 1), (1, 0)]), 'red')
  ]

  # A list of all the parts available. This is actually a string, but we make it
  # from the part names so we don't forget anyone.
  def __init__(self, target, parts):
    self.target = target
    self.parts = parts

class BoardState:

  framenr = 0
  logger = logging.getLogger('Board')
  extents = Point()

  def __init__(self, target, parts_placed, parts_available):
      self.target = target
      self.parts_placed = parts_placed
      self.parts_available = parts_available

  def plot(self, caption = '', movingpart = None, candidatepositions = None, deadpart = None):
  
    fig = plt.figure(1, figsize=(5,5), dpi=90)
    ax = fig.add_subplot(1,1,1) # rows, columns, index

    xoffset = 0
    yoffset = 0
    
    # plot the target polygon
    patch = PolygonPatch(self.target, facecolor='#cccccc')
    ax.add_patch(patch)
    BoardState.extents = BoardState.extents.union(self.target)

    # plot the placed parts on top of the target
    for part in self.parts_placed:
        polygon = part.finalpolygon()
        BoardState.extents = BoardState.extents.union(polygon)
        patch = PolygonPatch(polygon, facecolor=part.color)
        ax.add_patch(patch)
    
    # plot the available parts off to the side.
    bounds = self.target.bounds
    xoffset = bounds[0] # minx
    yoffset = bounds[1]-4 # miny and down from there
    for part in self.parts_available:
        polygon = translate(part.polygon, xoffset, yoffset)
        BoardState.extents = BoardState.extents.union(polygon)
        patch = PolygonPatch(polygon, facecolor=part.color)
        ax.add_patch(patch)

        # is this the dead part?
        if deadpart and (deadpart.name == part.name):
          patch = PolygonPatch(polygon, facecolor=part.color, edgecolor="red")
          ax.add_patch(patch)

        xoffset = xoffset + 4
        if xoffset > 12:
            xoffset = 0
            yoffset = yoffset - 4

    # plot the part that is on the move
    if movingpart:
        #self.logger.debug('movingpart xoffset={xoffset}, yoffset={yoffset}, rotation={rotation}'.format(xoffset=movingpart.xoffset, yoffset=movingpart.yoffset, rotation=movingpart.rotation))
        polygon = movingpart.finalpolygon()
        BoardState.extents = BoardState.extents.union(polygon)
        patch = PolygonPatch(polygon, facecolor=movingpart.color, alpha=0.5)
        ax.add_patch(patch)

    # plot candidatepositions
    if candidatepositions:
      for part in candidatepositions:
        polygon = part.finalpolygon()
        BoardState.extents = BoardState.extents.union(polygon)
        patch = PolygonPatch(polygon, facecolor=part.color, alpha=0.2)
        ax.add_patch(patch)

    bounds = BoardState.extents.bounds

    ax.set_title('FridgeIQ')
    xrange = [bounds[0]-1, bounds[2]+1]
    yrange = [bounds[1]-1, bounds[3]+1]
    ax.set_xlim(*xrange)
    ax.set_ylim(*yrange)
    ax.set_aspect(1)
    global runfolder
    figname = runfolder + '\\{n:05d}'.format(n=BoardState.framenr)
    if caption:
      figname += '_' + caption
    figname += '.png'
    fig.savefig(figname)
    plt.close(fig)
    BoardState.framenr += 1

def overlap(bounds1, bounds2):
  minx1 = bounds1[0]
  miny1 = bounds1[1]
  maxx1 = bounds1[2]
  maxy1 = bounds1[3]

  minx2 = bounds2[0]
  miny2 = bounds2[1]
  maxx2 = bounds2[2]
  maxy2 = bounds2[3]

  if (maxx1 <= minx2):
    return False # to the left
  elif (minx1 >= maxx2):
    return False # to the right
  elif (maxy1 <= miny2):
    return False # above
  elif (miny1 >= maxy2):
    return False # below
  else:
    return True # overlapping

def solve(board):

  indent = "  " * len(board.parts_placed)
    
  global finalpositions
  global plotsolutions
  global plotcandidates
  global plotdeadends
  global plotstepbystep

  if not board.parts_available:
    # No more parts to place. We are done.
    finalpositions += 1
    logger.info(indent + 'Found a solution! Checked {finalpositions} final positions.'.format(
      finalpositions=finalpositions
    ))

    wav = simpleaudio.WaveObject.from_wave_file(os.path.dirname(os.path.realpath(__file__)) + '\\fanfare.wav')
    wav.play()

    if plotsolutions:
      board.plot('solution')
  else:
    # Optimization: Check wether the smallest remaining disjoint area is still
    # applicable for the smallest part. If not we are already done with this whole
    # tree.
    if board.target.geom_type == 'MultiPolygon':
      min_target_area = min(board.target, key=lambda x: x.area).area
    else:
      min_target_area = board.target.area 
    
    min_part = min(board.parts_available, key=lambda x: x.polygon.area)

    if min_target_area < min_part.polygon.area:
      finalpositions += 1
      logger.debug(indent + 'Dead end: Minimum disjoint space {min_target_area} too small for minimum piece. Checked {finalpositions} final positions.'.format(
          min_target_area=min_target_area,
          finalpositions=finalpositions))
      
      if plotdeadends:
        board.plot('deadend_area', None, None, min_part)
      
      return

    # pick the next part to place.
    nextpart = board.parts_available[0]

    # Generate all possible legal positions nextpart can go in. This is
    # done in a discrete fashion by scanning the bounding box of the candidate
    # part in steps over the bounds of the target and checking the conditions.
    # The scanning happens in steps and is repeated for each possible 45 degree
    # rotation.
    targetbounds = board.target.bounds
    targetwidth = targetbounds[2]-targetbounds[0]
    targetheight = targetbounds[3]-targetbounds[1]

    nextpart.candidatepositions = []
      
    for rotation in nextpart.rotations:
      # Clone part in default position 
      part = copy.deepcopy(nextpart)

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

          # What about this position?
          testpoly = part.finalpolygon()

          # Condition 1:
          # The candidate part has to be completely inside the target          
          if board.target.contains(testpoly):
            # We have removed all the area covered by parts already placed
            # from the target. So we do not need to check for overlaps with
            # placed parts, this is covered in condition 1.
            # So we have a valid new legal position.                    
            nextpart.candidatepositions.append(copy.deepcopy(part))

          yoffset = yoffset + 1
        xoffset = xoffset + 1
      
    if len(nextpart.candidatepositions) == 0:
      finalpositions += 1
      logger.debug(indent + 'Dead end: Found no candidate positions for part {name}. Checked {finalpositions} final positions.'.format(
          name=nextpart.name,
          finalpositions=finalpositions))
      
      if plotdeadends:
        board.plot('deadend_nopos', None, None, nextpart)
      
      return    
      
    logger.debug(indent + 'Try part {name} with {candidatepositions} candidate positions next.'.format(
      name=nextpart.name,
      candidatepositions=len(nextpart.candidatepositions)
    ))

    if plotcandidates:
      board.plot('candidatepositions', None, nextpart.candidatepositions, nextpart)

    # try each candidate position
    i = 1
    for candidate in nextpart.candidatepositions:        
      logger.debug(indent + '{parts_placed} of {parts_total} parts placed. Try candidate position {i} of {candidatepositions} for part {name}.'.format(
        parts_placed=len(board.parts_placed), 
        parts_total=len(board.parts_placed) + len(board.parts_available), 
        i=i, 
        candidatepositions=len(nextpart.candidatepositions),
        name=nextpart.name
      ))

      # Prepare the next board by deep-copying the current one. Remove the part we
      # just (tentatively) placed from the list of available parts. Append it to
      # the placed parts and remove it from the target area.
      next_board = copy.deepcopy(board)
      next_board.parts_available = [part for part in next_board.parts_available if part.name != nextpart.name]
      next_board.parts_placed.append(candidate)
      next_board.target = next_board.target.difference(candidate.finalpolygon())
      
      if plotstepbystep:
        next_board.plot('try{i:02d}'.format(i=i), candidate)

      solve(next_board)
      i += 1

# set up logging
fh = logging.FileHandler(runfolder + '\\FridgeIQ.log')
fh.setLevel(logging.DEBUG)

ch = logging.StreamHandler()
ch.setLevel(logging.DEBUG)

ch.setFormatter(logging.Formatter('({thread}) [{levelname:7}] {name} - {message}', style='{'))
fh.setFormatter(logging.Formatter('{asctime} ({thread}) [{levelname:7}] {name} - {message}', style='{'))

root = logging.getLogger()
root.addHandler(ch)
root.addHandler(fh)
root.setLevel(logging.DEBUG)

logging.getLogger('matplotlib').setLevel(logging.INFO)

logger = logging.getLogger('Main')
logger.info('starting')

def solvepuzzle(puzzle):
  # Make a list of parts for the puzzle. Sort by descending area.
  parts = [p for p in Puzzle.partscatalog if p.name in list(puzzle.parts)]
  parts.sort(key=lambda part: (part.polygon.area, part.name), reverse=True) 

  # Plot some information about the puzzle initial state
  logger.debug('Target area={area}'.format(area=puzzle.target.area))
  logger.debug('Parts available in descending order of area:')
  totalarea = 0
  for part in parts:
    logger.debug('{name}: area={area}, distinct rotations={rotations}'.format(name=part.name, area=part.polygon.area, rotations=part.rotations))
    totalarea += part.polygon.area
  logger.debug('Total area of parts={totalarea}'.format(totalarea=totalarea))
  if totalarea == puzzle.target.area:
    logger.debug('Total parts area matches target area. A valid puzzle.')
  else:
    raise ValueError('Total parts area does not match target area, puzzle is invalid.')

  # Create the initial board state
  board = BoardState(puzzle.target, [], parts)

  # Try to solve it
  board.plot('setup')
  solve(board)

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

# Create string naming all parts
allparts = ''.join(map(lambda part: part.name, Puzzle.partscatalog))

# Set up the default puzzles. Each as a string and we can make a list of parts for
# them from the catalog if we want.
puzzles = {
  'square_1':  Puzzle(target_square(3), 'IJMR'),
  'square_2':  Puzzle(target_square(4), 'BDJNQSY'),
  'square_3':  Puzzle(target_square(4), 'ADJMNSY'),
  'square_4':  Puzzle(target_square(4), 'AIJMOQS'),
  'square_5':  Puzzle(target_square(5), 'ABDEIMNYRST'),
  'square_6':  Puzzle(target_square(5), 'ABDMNOQRSTY'),
  'square_7':  Puzzle(target_square(5), 'ABDEIJMNOSY'),
  'square_8':  Puzzle(target_square(5), 'ABIJMOQRSTY'),
  'square_9':  Puzzle(target_square(6), 'ARELOMSQJBNYIU'),
  'square_10': Puzzle(target_square(6), 'ARELOMTSQDJBNYI'),

  'challenge_1': Puzzle(target_octagon(), allparts)
}

solvepuzzle(puzzles['challenge_1'])

#input('Press Enter to continue...')
