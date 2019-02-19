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
import datetime
import argparse 

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

# Global variables
starttime = datetime.datetime.now().replace(microsecond=0)
options = None
puzzles = None
finalpositions = 0
solutions = 0

class Part:
  
  def __init__(self, name, polygon, color):
    self.name = name
    self.polygon = polygon
    self.color = color
    self.xoffset = 0
    self.yoffset = 0
    self.rotation = 0
    self.candidatepositions = []

    # build a list of distinct rotations
    self.rotations = [0]
    rotation_polys = [self.polygon]
    for rotation in range(90, 360, 90):
      test = rotate(self.polygon, rotation)
      if not any(test.equals(poly) for poly in rotation_polys):
        self.rotations.append(rotation)
        rotation_polys.append(test)

  def __copy__(self):
    clone = Part(self.name, self.polygon, self.color)
    clone.xoffset = self.xoffset
    clone.yoffset = self.yoffset
    clone.rotation = self.rotation
    clone.candidatepositions = self.candidatepositions.copy()

    return clone

  def finalpolygon(self):
    return translate(rotate(self.polygon, self.rotation), self.xoffset, self.yoffset)

class Puzzle:
  # Create a list of all the parts that make up the puzzle.
  partscatalog = [
    Part('A', Polygon([(0, 0), (1, 0), (1, 1), (2, 1), (1, 2), (0, 2), (0, 0)]), 'firebrick'),
    Part('R', Polygon([(1, 0), (2, 0), (2, 2), (1, 2), (0, 1), (1, 1), (1, 0)]), 'green'),
    Part('E', Polygon([(1, 0), (2, 0), (2, 2), (1, 2), (0, 1), (1, 1), (1, 0)]), 'blue'),
    Part('L', Polygon([(0, 0), (2, 0), (2, 1), (3, 1), (2, 2), (1, 2), (1, 1), (0, 1), (0, 0)]), 'purple'),
    Part('O', Polygon([(0, 0), (2, 0), (1, 1), (1, 2), (0, 2), (0, 0)]), 'yellow'),
    Part('M', Polygon([(0, 0), (1, 0), (1, 2), (0, 1), (0, 0)]), 'firebrick'),
    Part('T', Polygon([(0, 0), (3, 0), (1, 2), (1, 1), (0, 1), (0, 0)]), 'green',),
    Part('S', Polygon([(0, 0), (1, 0), (1, 3), (0, 2), (0, 0)]), 'blue'),
    Part('Q', Polygon([(0, 0), (1, 0), (1, 2), (0, 2), (0, 0)]), 'purple'),
    Part('D', Polygon([(0, 0), (2, 0), (1, 1), (0, 0)]), 'yellow'),
    Part('J', Polygon([(0, 0), (2, 0), (2, 2), (1, 2), (1, 1), (0, 1), (0, 0)]), 'firebrick'),
    Part('B', Polygon([(0, 0), (2, 0), (2, 1), (0, 1), (0, 0)]), 'green'),
    Part('N', Polygon([(0, 0), (1, 0), (1, 1), (3, 1), (3, 2), (0, 2), (0, 0)]), 'blue'),
    Part('Y', Polygon([(0, 0), (1, 0), (1, 1), (0, 2), (0, 0)]), 'purple'),
    Part('I', Polygon([(0, 0), (2, 0), (2, 2), (0, 0)]), 'yellow'),
    Part('U', Polygon([(1, 0), (2, 0), (2, 2), (1, 2), (1, 3), (0, 3), (0, 1), (1, 1), (1, 0)]), 'firebrick')
  ]

  # Create string naming all parts
  allparts = ''.join(map(lambda part: part.name, partscatalog))

  def __init__(self, name, target, parts):
    self.name = name
    self.target = target
    self.parts = parts

  # Helper function to create a rect of given dimensions as a target shape.
  @classmethod
  def target_rect(cls, width, height):
    return Polygon([(0, 0), (width, 0), (width, height), (0, height), (0, 0)])

  # Helper function to create a square of given side-length as a target shape.
  @classmethod
  def target_square(cls, sides):
    return Puzzle.target_rect(sides, sides)

  # Helper function to create a rect-triangle of given side-length as a target shape.
  @classmethod
  def target_triangle(cls, side):
    return Polygon([(0, 0), (side, 0), (side, side), (0, 0)])

  # Helper function to create a rect-triangle of given side-length as a target shape.
  @classmethod
  def target_triangle_horz(cls, base, height):
    return Polygon([(0, 0), (base, 0), (base/2, height), (0, 0)])

  # Helper function to the target shape for a challenge.
  @classmethod
  def target_challenge_1(cls):
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

  # Helper function to the target shape for a challenge.
  @classmethod
  def target_challenge_2(cls):
    return Polygon([
      (3, 0),
      (5, 0), (5, 1), (6, 1), (6, 2), (7, 2), (7, 3), (8, 3),
      (8, 5), (7, 5), (7, 6), (6, 6), (6, 7), (5, 7), (5, 8),
      (3, 8), (3, 7), (2, 7), (2, 6), (1, 6), (1, 5), (0, 5),
      (0, 3), (1, 3), (1, 2), (2, 2), (2, 1), (3, 1), (3, 0) 
    ])

  # Helper function to the target shape for a challenge.
  @classmethod
  def target_challenge_3(cls):
    outer =  Polygon([
      (1, 0),
      (3, 0), (3, 1), (4, 1), (4, 0), (6, 0), (6, 1), (7, 1),
      (7, 3), (6, 3), (6, 4), (7, 4), (7, 6), (6, 6), (6, 7),
      (4, 7), (4, 6), (3, 6), (3, 7), (1, 7), (1, 6), (0, 6),
      (0, 4), (1, 4), (1, 3), (0, 3), (0, 1), (1, 1), (1, 0) 
    ])

    mid = 3.5
    hole = 0.5
    inner = Polygon([
      (mid-hole, mid-hole),
      (mid+hole, mid-hole),
      (mid+hole, mid+hole),
      (mid-hole, mid+hole),
      (mid-hole, mid-hole)
    ])

    return outer.difference(inner)

  # Helper function to the target shape for a challenge.
  @classmethod
  def target_challenge_4(cls):
    outer =  Polygon([(0, 0), (7, 0), (7, 7), (0, 7), (0, 0)])

    mid = 3.5
    hole = 0.5
    inner = Polygon([
      (mid-hole, 1),
      (mid+hole, 1),
      (mid+hole, mid-hole),
      (6, mid-hole),
      (6, mid+hole),
      (mid+hole, mid+hole),
      (mid+hole, 6),
      (mid-hole, 6),
      (mid-hole, mid+hole),
      (1, mid+hole),
      (1, mid-hole),
      (mid-hole, mid-hole),
      (mid-hole, 1)
    ])

    return outer.difference(inner)

  # Helper function to the target shape for a challenge.
  @classmethod
  def target_challenge_5(cls):
    outer = Polygon([
      (3, 0),
      (5, 0), (5, 1), (6, 1), (7, 2), (7, 3), (8, 3),
      (8, 5), (7, 5), (7, 6), (6, 7), (5, 7), (5, 8),
      (3, 8), (3, 7), (2, 7), (1, 6), (1, 5), (0, 5),
      (0, 3), (1, 3), (1, 2), (2, 1), (3, 1), (3, 0) 
    ])

    mid = 4
    hole = 1
    inner = Polygon([
      (mid-hole, mid),
      (mid,      mid-hole),
      (mid+hole, mid),
      (mid,      mid+hole),
      (mid-hole, mid)
    ])

    return outer.difference(inner)

  # Helper function to the target shape for a challenge.
  @classmethod
  def target_challenge_6(cls):
    outer =  Polygon([
      (0, 0),
      (3, 0), (3, 2), (4, 2), (4, 0), (7, 0),
      (7, 3), (5, 3), (5, 4), (7, 4), (7, 7),
      (4, 7), (4, 5), (3, 5), (3, 7), (0, 7),
      (0, 4), (2, 4), (2, 3), (0, 3), (0, 0) 
    ])

    mid = 3.5
    hole = 0.5
    inner = Polygon([
      (mid-hole, mid-hole),
      (mid+hole, mid-hole),
      (mid+hole, mid+hole),
      (mid-hole, mid+hole),
      (mid-hole, mid-hole)
    ])

    return outer.difference(inner)

class BoardState:

  framenr = 0
  logger = logging.getLogger('Board')
  extents = Point()

  def __init__(self, puzzle, parts_placed, parts_available):
    self.puzzle = puzzle
    self.target = puzzle.target
    self.parts_placed = parts_placed
    self.parts_available = parts_available
    self.candidateposition = None

  def __copy__(self):
    clone = BoardState(self.target, self.parts_placed.copy(), self.parts_available.copy())
    clone.puzzle = self.puzzle

    return clone 

  def filter_rotational_symmetries(self, boards):
    # given a list of board states, return the list of those that do not
    # have 90-degree rotational symmetries with any others.
    result = []

    if boards:
      # We assume that all the boards are for the same puzzle, that is their 
      # complete targets are the same. So we can rotate around the common 
      # center of the original target.
      center = boards[0].puzzle.target.centroid
      
      for board in boards:
        matches = False
      
        # check each rotation against each entry already in result.
        for rotation in range(0, 360, 90):
          comparepoly = rotate(board.target, rotation, center)
          for res in result:
            if comparepoly.equals(res.target):
              matches = True
              break
          if matches:
            break
        
        if not matches:
          result.append(board)
          #board.plot('filter_append_' +  str(matches))

    return result

  def plot(self, caption = '', movingpart = None, candidatepositions = None, deadpart = None):
    
    global options

    fig = plt.figure(1, figsize=(5,5), dpi=90)
    ax = fig.add_subplot(1,1,1) # rows, columns, index
    
    # no axes ticks
    ax.yaxis.set_major_locator(plt.NullLocator())
    ax.xaxis.set_major_formatter(plt.NullFormatter())
    ax.yaxis.set_minor_locator(plt.NullLocator())
    ax.xaxis.set_minor_formatter(plt.NullFormatter())

    xoffset = 0
    yoffset = 0
    
    # plot the target polygon
    if (self.target.geom_type == 'MultiPolygon') or (self.target.geom_type == 'Polygon'):
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
    if self.parts_available:
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
          patch = PolygonPatch(polygon, facecolor=part.color, edgecolor='red')
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
    
    figname = options.runfolder + '\\{n:05d}'.format(n=BoardState.framenr)
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

  global finalpositions
  global solutions
  global options
  
  logger = logging.getLogger('solve')

  indent = '  ' * len(board.parts_placed)
  
  if not board.parts_available:
    # No more parts to place. We are done.
    finalpositions += 1
    logger.info('Found a solution! Checked {finalpositions} final positions.'.format(
      finalpositions=finalpositions
    ))

    solutions += 1

    if options.playfanfare:
      wav = simpleaudio.WaveObject.from_wave_file(os.path.dirname(os.path.realpath(__file__)) + '\\fanfare.wav')
      wav.play()

    if options.plotsolutions:
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
      
      if options.plotdeadends:
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
      part = copy.copy(nextpart)

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
            nextpart.candidatepositions.append(copy.copy(part))

          yoffset = yoffset + 1
        xoffset = xoffset + 1
      
    if len(nextpart.candidatepositions) == 0:
      finalpositions += 1
      logger.debug(indent + 'Dead end: Found no candidate positions for part {name}. Checked {finalpositions} final positions.'.format(
        name=nextpart.name,
        finalpositions=finalpositions))
      
      if options.plotdeadends:
        board.plot('deadend_nopos',None, None, nextpart)
      
      return    

    logger.debug(indent + 'Creating next boards for part {name} with {candidatepositions} candidate positions'.format(
      name=nextpart.name,
      candidatepositions=len(nextpart.candidatepositions)))

    # For each candidate position prepare a list of next boards by copying 
    # the current one. Remove the part we just (tentatively) placed from the list
    # of available parts. Append it to the placed parts and remove it from the 
    # target area.
    nextboards = []
    for candidate in nextpart.candidatepositions:    
      nextboard = copy.deepcopy(board)
      nextboard.parts_available = [part for part in nextboard.parts_available if part.name != nextpart.name]
      nextboard.candidateposition = candidate
      nextboard.parts_placed.append(candidate)
      nextboard.target = nextboard.target.difference(candidate.finalpolygon())

      nextboards.append(nextboard)
      
    # Filter next boards to eliminate the ones with rotational symmetry
    nextboards = board.filter_rotational_symmetries(nextboards)

    msg = indent + 'Try part {name} with {nextboards} candidate positions'.format(
      name=nextpart.name,
      nextboards=len(nextboards),
      candidatepositions=len(nextpart.candidatepositions)
    )
    if len(nextpart.candidatepositions) != len(nextboards):
      msg += ' (down from {candidatepositions})'.format(candidatepositions=len(nextpart.candidatepositions))
    msg += ' next.'
    logger.debug(msg)

    # update candidatepositions to include any filtering that has happened.
    nextpart.candidatepositions = list(map(lambda board: board.candidateposition, nextboards))
    
    if options.plotcandidates:
      board.plot('candidatepositions', None, nextpart.candidatepositions)

    # try each candidate position
    i = 1
    for nextboard in nextboards:        
      logger.debug(indent + '{parts_placed} of {parts_total} parts placed. Try next position {i} of {nextboards} for part {name}.'.format(
        parts_placed=len(board.parts_placed), 
        parts_total=len(board.parts_placed) + len(board.parts_available), 
        i=i, 
        nextboards=len(nextboards),
        name=nextpart.name
      ))

      if options.plotstepbystep:
        nextboard.plot('try{i:02d}'.format(i=i), nextboard.candidateposition)

      solve(nextboard)
      i += 1

def solvepuzzle(puzzle):

  global options
  
  logger = logging.getLogger('solvepuzzle')

  # Make a list of parts for the puzzle. Sort by descending area.
  parts = [p for p in Puzzle.partscatalog if p.name in list(puzzle.parts)]
  parts.sort(key=lambda part: (part.polygon.area, part.name), reverse=True) 

  # Create the initial board state
  board = BoardState(puzzle, [], parts)

  # Plot initial board state
  board.plot('setup')

  # Print some information about the puzzle initial state
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

  # Try to solve it
  solve(board)

# Set up the default puzzles. Each as a string and we can make a list of parts for
# them from the catalog if we want.
def create_puzzles():

  global puzzles

  puzzles = [
    Puzzle('square_01', Puzzle.target_square(3), 'IJMR'),
    Puzzle('square_02', Puzzle.target_square(4), 'BDJNQSY'),
    Puzzle('square_03', Puzzle.target_square(4), 'ADJMNSY'),
    Puzzle('square_04', Puzzle.target_square(4), 'AIJMOQS'),
    Puzzle('square_05', Puzzle.target_square(5), 'ABDEIMNYRST'),
    Puzzle('square_06', Puzzle.target_square(5), 'ABDMNOQRSTY'),
    Puzzle('square_07', Puzzle.target_square(5), 'ABDEIJMNOSY'),
    Puzzle('square_08', Puzzle.target_square(5), 'ABIJMOQRSTY'),
    Puzzle('square_09', Puzzle.target_square(6), 'ARELOMSQJBNYIU'),
    Puzzle('square_10', Puzzle.target_square(6), 'ARELOMTSQDJBNYI'),

    # Rectangular challenges. Lists all integer-sided rectangles that can be
    # made from the total area given by the prescribed parts list.

    # area = 8 = 2*2*2
    Puzzle('rectangle_01', Puzzle.target_rect(2*2, 2), 'ABDE'),
    
    # area = 12 = 2*2*3
    Puzzle('rectangle_02_a', Puzzle.target_rect(2, 2*3), 'IQRST'),
    #Puzzle('rectangle_02_b', target_rect(2*2, 3), 'IQRST'), # Valid total area, no solution
    
    # area = 15 = 5*3
    Puzzle('rectangle_03', Puzzle.target_rect(5, 3), 'DEIMOST'),

    # area = 20 = 5*2*2
    Puzzle('rectangle_04_a', Puzzle.target_rect(5, 2*2), 'ABDEJORU'),
    Puzzle('rectangle_04_b', Puzzle.target_rect(5*2, 2), 'ABDEJORU'),

    # area = 20 = 5*2*2
    Puzzle('rectangle_05_a', Puzzle.target_rect(5, 2*2), 'ADELMORSY'),
    Puzzle('rectangle_05_b', Puzzle.target_rect(5*2, 2), 'ADELMORSY'),

    # area = 20 = 5*2*2
    Puzzle('rectangle_06_a', Puzzle.target_rect(5, 2*2), 'ABEIJMOSY'),
    Puzzle('rectangle_06_b', Puzzle.target_rect(5*2, 2), 'ABEIJMOSY'),

    # area = 24 = 3*2*2*2
    Puzzle('rectangle_07_a', Puzzle.target_rect(3, 2*2*2), 'ABEIMNOSTY'),
    Puzzle('rectangle_07_b', Puzzle.target_rect(3*2, 2*2), 'ABEIMNOSTY'),
    Puzzle('rectangle_07_c', Puzzle.target_rect(3*2*2, 2), 'ABEIMNOSTY'),

    # area = 30 = 3*5*2 
    Puzzle('rectangle_08_a', Puzzle.target_rect(3, 5*2), 'IJLMNORSTUY'),
    Puzzle('rectangle_08_b', Puzzle.target_rect(5, 3*2), 'IJLMNORSTUY'),
    Puzzle('rectangle_08_c', Puzzle.target_rect(2, 5*3), 'IJLMNORSTUY'),

    # area = 28 = 7*2*2
    Puzzle('rectangle_09_a', Puzzle.target_rect(7, 2*2), 'ABDJLMNRSUY'),
    Puzzle('rectangle_09_b', Puzzle.target_rect(7*2, 2), 'ABDJLMNRSUY'),

    # area = 40 = 2*2*2*5
    Puzzle('rectangle_10_a', Puzzle.target_rect(2, 2*2*5), Puzzle.allparts),
    Puzzle('rectangle_10_b', Puzzle.target_rect(5, 2*2*2), Puzzle.allparts),
    Puzzle('rectangle_10_c', Puzzle.target_rect(2*2, 2*5), Puzzle.allparts),
    Puzzle('rectangle_10_d', Puzzle.target_rect(2*5, 2*2), Puzzle.allparts),

    Puzzle('triangle_01', Puzzle.target_triangle(3), 'DIY'),            # area = 4.5  
    Puzzle('triangle_02', Puzzle.target_triangle(5), 'AIOST'),          # area = 12.5
    Puzzle('triangle_03', Puzzle.target_triangle(5), 'DJMSTY'),         # area = 12.5
    Puzzle('triangle_04', Puzzle.target_triangle_horz(8,4), 'DEMRTUY'), # area = 16
    Puzzle('triangle_05', Puzzle.target_triangle(6), 'BDIMQRSTY'),      # area = 18
    Puzzle('triangle_06', Puzzle.target_triangle(7), 'DEIJLMNOTY'),     # area = 24.5
    Puzzle('triangle_07', Puzzle.target_triangle(7), 'ADILMOQRSTY'),    # area = 24.5
    Puzzle('triangle_08', Puzzle.target_triangle(7), 'ABDIMNOQSTY'),    # area = 24.5
    Puzzle('triangle_09', Puzzle.target_triangle(8), 'ARELTSQDJBNYI'),  # area = 32
    Puzzle('triangle_10', Puzzle.target_triangle(8), 'ARELOMTSQDJBYI'), # area = 32

    Puzzle('challenge_01', Puzzle.target_challenge_1(), Puzzle.allparts),
    Puzzle('challenge_02', Puzzle.target_challenge_2(), Puzzle.allparts),
    Puzzle('challenge_03', Puzzle.target_challenge_3(), Puzzle.allparts),
    Puzzle('challenge_04', Puzzle.target_challenge_4(), Puzzle.allparts),
    Puzzle('challenge_05', Puzzle.target_challenge_5(), Puzzle.allparts),
    Puzzle('challenge_06', Puzzle.target_challenge_6(), Puzzle.allparts)
  ]

def parse_commandline():

  global options
  global puzzles

  parser = argparse.ArgumentParser(
      description = 'Solve FridgeIQ-puzzles.', 
      epilog = 'valid puzzle names are: ' + ',\n'.join(map(lambda puzzle: puzzle.name, puzzles)) + ').'
  )

  parser.add_argument('-pn', '--puzzle', 
    action = 'store', 
    default = 'rectangle_04_a', 
    help = 'Select the puzzle to be solved from the internal list of configurations (default: %(default)s)', 
    metavar = 'name',
    dest = 'puzzle_name'
  )

  parser.add_argument('-ll', '--log-level',
    action = 'store',
    default = 'INFO',
    help ='Set the logging output level to CRITICAL, ERROR, WARNING, INFO or DEBUG (default: %(default)s)',
    dest ='log_level',
    metavar = 'level'
  )

  parser.add_argument('-pc', '--plot-candidates',
    action = 'store',
    default = False,
    type = bool,
    help = 'Output a frame showing all generated candidate positions shaded (default: %(default)s)',
    dest = 'plotcandidates',
    metavar = 'flag'
  )

  parser.add_argument('-pd', '--plot-deadends',
    action = 'store',
    default = False,
    type = bool,
    help = 'Output a frame showing each dead-end position (default: %(default)s)',
    dest = 'plotdeadends',
    metavar = 'flag'
  )

  parser.add_argument('-ps', '--plot-solutions',
    action = 'store',
    default = True,
    type = bool,
    help = 'Output a frame showing each solution (default: %(default)s)',
    dest = 'plotsolutions',
    metavar = 'flag'
  )

  parser.add_argument('-pb', '--plot-step-by-step',
    action = 'store',
    default = False,
    type = bool,
    help = 'Output a frame showing each candidate position as it is tried (default: %(default)s)',
    dest = 'plotstepbystep',
    metavar = 'flag'
  )

  parser.add_argument('-of', '--output_folder',
    action = 'store',
    default = '',
    help = 'Folder for output artefacts (default: puzzle_name and timestamp)',
    dest = 'runfolder',
    metavar = 'folder'
  )

  parser.add_argument('-pf', '--play-fanfare',
    action = 'store',
    default = True,
    type = bool,
    help = 'Play a fanfare whenever a solution is found (default: %(default)s)',
    dest = 'playfanfare',
    metavar = 'flag'
  )

  options = parser.parse_args()
  options.log_level_int = getattr(logging, options.log_level, logging.INFO)

  if not options.runfolder:
    options.runfolder = os.path.dirname(os.path.realpath(__file__)) + '\\' + options.puzzle_name + '_' + time.strftime('%Y-%m-%d-%H-%M-%S', time.localtime())
      
def setup_logging():
  
  global options
  
  os.makedirs(options.runfolder)

  # set up logging
  fh = logging.FileHandler(options.runfolder + '\\FridgeIQ.log')
  fh.setLevel(options.log_level_int)

  ch = logging.StreamHandler()
  ch.setLevel(options.log_level_int)

  ch.setFormatter(logging.Formatter('({thread}) [{levelname:7}] {name} - {message}', style='{'))
  fh.setFormatter(logging.Formatter('{asctime} ({thread}) [{levelname:7}] {name} - {message}', style='{'))

  root = logging.getLogger()
  root.addHandler(ch)
  root.addHandler(fh)
  root.setLevel(logging.DEBUG)

  logging.getLogger('matplotlib').setLevel(logging.INFO)

def main():
  
  global options
  global puzzles

  create_puzzles()
  parse_commandline()
  setup_logging()

  logger = logging.getLogger('main')
  logger.info('Starting. Output goes to {runfolder}'.format(runfolder=options.runfolder))

  findpuzzle = list(filter(lambda puzzle: puzzle.name == options.puzzle_name, puzzles))
  if not findpuzzle:
    raise ValueError('Puzzle name "{puzzle}" not found.'.format(puzzle=options.puzzle_name))

  logger.info('Attempting to solve puzzle "{puzzle}". This may take a while...'.format(puzzle=options.puzzle_name))

  puzzle = list(filter(lambda puzzle: puzzle.name == options.puzzle_name, puzzles))[0]
  solvepuzzle(puzzle)

  logger.info('{solutions} solutions found.'.format(solutions=solutions))

  endtime = datetime.datetime.now().replace(microsecond=0)
  runtime = (endtime-starttime)
  logger.info('Finished. Total runtime: {runtime}'.format(runtime=runtime))

  #input('Press Enter to continue...')
    
if __name__ == '__main__':
    main()