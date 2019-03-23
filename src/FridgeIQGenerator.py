# -*- coding: utf-8 -*-
'''
@author: Marian Aldenhövel <marian.aldenhoevel@marian-aldenhoevel.de>
'''
# This is a program to generate symmetric challenges_found for the FridgeIQ puzzle.
# It uses the z3 SAT/SMT solver for the heavy lifting.

import random
import re
import math
import logging
import os
import sys
import time
import copy
import simpleaudio
import datetime
import argparse 
import math
import z3
import hashlib

from shapely.geometry.polygon import Polygon
from shapely.geometry.point import Point
from shapely.affinity import translate
from shapely.affinity import rotate
from descartes import PolygonPatch

import matplotlib
matplotlib.use('agg') # Select a non-interactive backend. Do this before importing pyplot!
from matplotlib import pyplot

# Global variables
starttime = datetime.datetime.now().replace(microsecond=0)
challenges_found = 0
options = None

# Part encapsulates a single part in the puzzle. It has geometry as a shapely.geometry.polygon which is
# never transformed after creation.
#
# When a Part is constructed __init__ checks the geometry to see in which of the 90-degree rotations it
# has distinct geometry. This list is also kept with the Part.
#
# Parts also hold a list of shards they cover. While this could be determined from the geometry I chose
# to use geometry for drawing and a discrete naming-scheme for the shards and make both by hand.
class Part:

  def __init__(self, name, polygon, color, shards):
    self.name = name
    self.polygon = polygon
    self.color = color
    self.placements = []
    self.shards = shards
    
    # build a list of distinct rotations
    self.rotations = [0]
    rotation_polys = [self.polygon]
    for rotation in range(90, 360, 90):
      test = rotate(self.polygon, rotation)
      if not any(test.equals(poly) for poly in rotation_polys):
        self.rotations.append(rotation)
        rotation_polys.append(test)

# A Shard is an individual section of the field that can be covered by a part.
# Based on the shape of the tiles four Shards are generated for each grid square.
# The square is disected into four triangles, one each to the east, west, north
# and south of the square, meeting with their apexes at the center. Either zero,
# two or four of those will be covered at any time.
# Shards are described by the y- and y-position of the bottom-left corner of the 
# grid square and the a one-letter abbreviation of the direction.
class Shard:

  logger = logging.getLogger('Shard')

  # Build the canonical name for a shard 
  @classmethod
  def makename(cls, xoffset, yoffset, direction):
    return '({x})-({y})-{direction}'.format(x=xoffset, y=yoffset, direction=direction)
   
  # Make a Shard from a canonical name, used in unit-testing.
  @classmethod
  def makeshard(cls, name):

    # Split the canonical name using a regular expression
    match = re.match(r'\((-?\d)\)-\((-?\d)\)-(.)', name)
    xoffset = int(match.group(1))
    yoffset = int(match.group(2))  
    direction = match.group(3)

    # Create a new shard with the same elements. This will thus have the same
    # canonical name.
    return Shard(xoffset, yoffset, direction)
  
  def __init__(self, xoffset, yoffset, direction):
    self.name = self.makename(xoffset, yoffset, direction)
    self.xoffset = xoffset
    self.yoffset = yoffset
    self.direction = direction
    self.placements = []

    # Make shapely geometry for the shard so we can plot it. To do that
    # find the four corners of the grid square and the midpoint. Then,
    # depending on the direction of the shard, pick the four points for
    # a shapely polygon.
    bl = Point(xoffset,        yoffset)
    br = Point(xoffset + 1,    yoffset)
    tr = Point(xoffset + 1,    yoffset + 1)
    tl = Point(xoffset,        yoffset + 1)
    mid = Point(xoffset + 0.5, yoffset + 0.5)
    
    if direction == "n":
      points = [mid, tr, tl, mid]
    elif direction == "e":
      points = [mid, tr, br, mid]
    elif direction == "w":
      points = [mid, tl, bl, mid]
    elif direction == "s":
      points = [mid, bl, br, mid]
      
    self.polygon = Polygon([[p.x, p.y] for p in points])
    
  # Return a new Shard that results from first rotating self around the origin 
  # by rotation degrees and then moving it by xoffset and yoffset 
  def transform(self, xoffset, yoffset, rotation):
    directions = list("nwse")

    if rotation == 0:
      x = self.xoffset
      y = self.yoffset
      diroffset = 0
    elif rotation == 90:
      x = -self.yoffset-1
      y = self.xoffset
      diroffset = 1
    elif rotation == 180:
      x = -self.xoffset-1
      y = -self.yoffset-1
      diroffset = 2
    elif rotation == 270:
      x = self.yoffset
      y = -self.xoffset-1
      diroffset = 3
    
    dirindex = directions.index(self.direction)
    direction = directions[(dirindex + diroffset) % 4]

    return Shard(x + xoffset, y + yoffset, direction)

  # Return the name of the shard that is horizontally mirrored across from here.
  # Version for even symmetry.
  def mirror_e_w_even(self):
    xoffset = -self.xoffset - 1
    yoffset = self.yoffset

    if self.direction == "w":
      direction = "e"
    elif self.direction == "e":
      direction = "w"
    else:
      direction = self.direction

    return Shard.makename(xoffset, yoffset, direction)

  # Return the name of the shard that is vertically mirrored up/down from here
  # Version for even symmetry.
  def mirror_n_s_even(self):
    xoffset = self.xoffset
    yoffset = -self.yoffset - 1
    
    if self.direction == "n":
      direction = "s"
    elif self.direction == "s":
      direction = "n"
    else:
      direction = self.direction

    return Shard.makename(xoffset, yoffset, direction)

  # Return the name of the shard that is mirrored across the sw-ne-diagonal
  # Version for even symmetry.
  def mirror_sw_ne_even(self):
    xoffset = self.yoffset
    yoffset = self.xoffset

    if self.direction == "n":
      direction = "e"
    elif self.direction == "e":
      direction = "n"
    elif self.direction == "w":
      direction = "s"
    elif self.direction == "s":
      direction = "w"
    else:
      direction = self.direction

    return Shard.makename(xoffset, yoffset, direction)

  # Return the name of the shard that is mirrored across the nw-se-diagonal
  # Version for even symmetry.
  def mirror_nw_se_even(self):
    xoffset = -self.yoffset - 1
    yoffset = -self.xoffset - 1

    if self.direction == "n":
      direction = "w"
    elif self.direction == "w":
      direction = "n"
    elif self.direction == "e":
      direction = "s"
    elif self.direction == "s":
      direction = "e"
    else:
      direction = self.direction

    return Shard.makename(xoffset, yoffset, direction)

  # Return the name of the shard that is horizontally mirrored across from here
  # Version for odd symmetry.
  def mirror_e_w_odd(self):
    xoffset = -self.xoffset
    yoffset = self.yoffset

    if self.direction == "w":
      direction = "e"
    elif self.direction == "e":
      direction = "w"
    else:
      direction = self.direction

    return Shard.makename(xoffset, yoffset, direction)

  # Return the name of the shard that is vertically mirrored up/down from here
  # Version for odd symmetry.
  def mirror_n_s_odd(self):
    xoffset = self.xoffset
    yoffset = -self.yoffset
    
    if self.direction == "n":
      direction = "s"
    elif self.direction == "s":
      direction = "n"
    else:
      direction = self.direction

    return Shard.makename(xoffset, yoffset, direction)

  # Return the name of the shard that is mirrored across the sw-ne-diagonal
  # Version for odd symmetry.
  def mirror_sw_ne_odd(self):
    xoffset = self.yoffset
    yoffset = self.xoffset

    if self.direction == "n":
      direction = "e"
    elif self.direction == "e":
      direction = "n"
    elif self.direction == "w":
      direction = "s"
    elif self.direction == "s":
      direction = "w"
    else:
      direction = self.direction

    return Shard.makename(xoffset, yoffset, direction)

  # Return the name of the shard that is mirrored across the nw-se-diagonal
  # Version for odd symmetry.
  def mirror_nw_se_odd(self):
    xoffset = -self.yoffset
    yoffset = -self.xoffset

    if self.direction == "n":
      direction = "w"
    elif self.direction == "w":
      direction = "n"
    elif self.direction == "e":
      direction = "s"
    elif self.direction == "s":
      direction = "e"
    else:
      direction = self.direction

    return Shard.makename(xoffset, yoffset, direction)

# Wraps a list and gives it a fluent API for building lists of shards that
# become part of the description of parts.
class ShardList:

  def __init__(self):
    self.list = []
    
  # Add up to four new shards to the list. If directions is ommited the
  # complete grid square indexed by xoffset and yoffset is covered by
  # four shards. If directions is given parts of that square can be covered
  # by less then four.
  def append(self, xoffset, yoffset, directions = "news"):
    for  direction in list(directions):
      self.list.append(Shard(xoffset, yoffset, direction))
    return self

  # Return a new list of shards that result from first rotating each of 
  # my shards around the origin by rotation degrees and then moving
  # it by xoffset and yoffset 
  def transform(self, xoffset, yoffset, rotation):
    result = ShardList()
    
    for shard in self.list:
      result.list.append(shard.transform(xoffset, yoffset, rotation))
    
    return result

# Build the catalog of parts that are in the FridgeIQ box.
# For each the visible geometry and the list of shards in their resting
# position is created. 
partscatalog = [
    Part('A', Polygon([(0, 0), (1, 0), (1, 1), (2, 1), (1, 2), (0, 2), (0, 0)]), 'firebrick', ShardList().append(0, 0).append(0, 1).append(1, 1, "ws")),
    Part('R', Polygon([(1, 0), (2, 0), (2, 2), (1, 2), (0, 1), (1, 1), (1, 0)]), 'green', ShardList().append(1, 0).append(1, 1).append(0, 1, "se")),
    Part('E', Polygon([(1, 0), (2, 0), (2, 2), (1, 2), (0, 1), (1, 1), (1, 0)]), 'blue', ShardList().append(1, 0).append(1, 1).append(0, 1, "se")),
    Part('L', Polygon([(0, 0), (2, 0), (2, 1), (3, 1), (2, 2), (1, 2), (1, 1), (0, 1), (0, 0)]), 'purple', ShardList().append(0, 0).append(1, 0).append(1, 1).append(2, 1, "ws")),
    Part('O', Polygon([(0, 0), (2, 0), (1, 1), (1, 2), (0, 2), (0, 0)]), 'yellow', ShardList().append(0, 0).append(0, 1).append(1, 0, "sw")),
    Part('M', Polygon([(0, 0), (1, 0), (1, 2), (0, 1), (0, 0)]), 'firebrick', ShardList().append(0, 0).append(0, 1, "se")),
    Part('T', Polygon([(0, 0), (3, 0), (1, 2), (1, 1), (0, 1), (0, 0)]), 'green', ShardList().append(0, 0).append(1, 0).append(1, 1, "sw").append(2, 0, "sw")),
    Part('S', Polygon([(0, 0), (1, 0), (1, 3), (0, 2), (0, 0)]), 'blue', ShardList().append(0, 0).append(0, 1).append(0, 2, "se")),
    Part('Q', Polygon([(0, 0), (1, 0), (1, 2), (0, 2), (0, 0)]), 'purple', ShardList().append(0, 0).append(0, 1)),
    Part('D', Polygon([(0, 0), (2, 0), (1, 1), (0, 0)]), 'yellow', ShardList().append(0, 0, "se").append(1, 0, "sw")),
    Part('J', Polygon([(0, 0), (2, 0), (2, 2), (1, 2), (1, 1), (0, 1), (0, 0)]), 'firebrick', ShardList().append(0, 0).append(1, 0).append(1, 1)),
    Part('B', Polygon([(0, 0), (2, 0), (2, 1), (0, 1), (0, 0)]), 'green', ShardList().append(0, 0).append(1, 0)),
    Part('N', Polygon([(0, 0), (1, 0), (1, 1), (3, 1), (3, 2), (0, 2), (0, 0)]), 'blue', ShardList().append(0, 0).append(0, 1).append(1, 1).append(2, 1)),
    Part('Y', Polygon([(0, 0), (1, 0), (1, 1), (0, 2), (0, 0)]), 'purple', ShardList().append(0, 0).append(0, 1, "sw")),
    Part('I', Polygon([(0, 0), (2, 0), (2, 2), (0, 0)]), 'yellow', ShardList().append(0, 0, "se").append(1, 0).append(1, 1, "se")),
    Part('U', Polygon([(1, 0), (2, 0), (2, 2), (1, 2), (1, 3), (0, 3), (0, 1), (1, 1), (1, 0)]), 'firebrick', ShardList().append(1, 0).append(1, 1).append(0, 1).append(0, 2))
  ]

allparts = ''.join(map(lambda part: part.name, partscatalog))

# Placement describes a specific part in a specific place on the field. This
# includes rotation and x- and y-position. Also holds geometry for the part
# in case we want to plot it later. And it keeps a list of shards that the
# part covers in this position.
# The final member of a Placement is a z3-Bool that indicates whether the
# part is actually at this placement or not in a solution.
class Placement:

  logger = logging.getLogger('Placement')

  def __init__(self, part, polygon, rotation, xoffset, yoffset):
  
    self.part = part
    self.polygon = polygon
    self.rotation = rotation
    self.xoffset = xoffset
    self.yoffset = yoffset

    self.shards = part.shards.transform(xoffset, yoffset, rotation) 

    self.xname = '{name}_{rotation}_{xoffset}_{yoffset}'.format(
      name = part.name,
      xoffset = xoffset,
      yoffset = yoffset,
      rotation = rotation
    )

    #self.logger.debug('Creating Placement with xname={xname}'.format(xname = xname))
    
    self.x = z3.Bool(self.xname)
  
# Conversion function for argparse booleans
def str2bool(v):
  if v.lower() in ('yes', 'true', 't', 'y', '1'):
    return True
  elif v.lower() in ('no', 'false', 'f', 'n', '0'):
    return False
  else:
    raise argparse.ArgumentTypeError('Boolean value expected.')

# Set up argparse and get the command line options.
def parse_commandline():

  global options
  global challenges_found

  parser = argparse.ArgumentParser(
      description = 'Generate FridgeIQ-challenges from a list of parts and a maximum size of playing field.', 
  )

  parser.add_argument('-ll', '--log-level',
    action = 'store',
    default = 'DEBUG',
    help ='Set the logging output level to CRITICAL, ERROR, WARNING, INFO or DEBUG (default: %(default)s)',
    dest ='log_level',
    metavar = 'level'
  )

  parser.add_argument('-of', '--output-folder',
    action = 'store',
    default = '',
    help = 'Folder for output artefacts (default: puzzle_name and timestamp)',
    dest = 'runfolder',
    metavar = 'folder'
  )

  parser.add_argument('-pf', '--play-fanfare',
    action = 'store',
    default = True,
    type = str2bool,
    help = 'Play a fanfare whenever a solution is found (default: %(default)s)',
    dest = 'playfanfare',
    metavar = 'flag'
  )

  parser.add_argument('-ho', '--horizon',
    action = 'store',
    default = 5,
    type = int,
    help = 'Half field-size (maximum absolute value of coordinates) to take into account (default: %(default)s)',
    dest = 'horizon',
    metavar = 'n'
  )

  parser.add_argument('-pl', '--parts-list',
    action = 'store',
    default = allparts,
    help = 'List of the part-names to be used (default: %(default)s)',
    dest = 'partslist',
    metavar = 'string'
  )

  parser.add_argument('-ss', '--save-state',
    action = 'store',
    default = 'Solver-State.smt2',
    help = 'If set saves and restores solver-state to and from the file. Attention! This can collide with other commandline-parameters and only works on similar setups (default: %(default)s)',
    dest = 'savestate',
    metavar = 'filename'
  )

  parser.add_argument('-sa', '--save-all',
    action = 'store',
    default = False,
    type = str2bool,
    help = 'Save all solutions to each challenge, false saves only the first solution found (default: %(default)s)',
    dest = 'saveall',
    metavar = 'flag'
  )

  parser.add_argument('-es', '--even-size',
    action = 'store',
    default = True,
    help = 'Generate challenges_found with even sizes (default: %(default)s)',
    dest = 'evensize',
    metavar = 'flag'
  )

  parser.add_argument('-os', '--odd-size',
    action = 'store',
    default = True,
    help = 'Generate challenges_found with odd sizes (default: %(default)s)',
    dest = 'oddsize',
    metavar = 'flag'
  )

  parser.add_argument('-zp', '--z3-parallel',
    action = 'store',
    default = True,
    help = 'Enable z3 parallel tactic (default: %(default)s)',
    dest = 'z3_parallel',
    metavar = 'flag'
  )

  options = parser.parse_args()
  options.log_level_int = getattr(logging, options.log_level, logging.INFO)

  if not options.runfolder:
    options.runfolder = os.path.dirname(os.path.realpath(__file__)) + '\\generator_' + time.strftime('%Y-%m-%d-%H-%M-%S', time.localtime())
  else:
    # If outputfolder is relative make it absolute to the script  
    if not os.path.isabs(options.runfolder):
      scriptdir = os.path.dirname(os.path.realpath(__file__))
      options.runfolder = os.path.abspath(os.path.join(scriptdir, options.runfolder))

  if options.savestate:
    # Add .smt2 extension unless an extension is already given.
    ext = os.path.splitext(options.savestate)[1]
    if not ext:
      options.savestate = options.savestate + '.smt2'

    # If save state is a relative path make it absolute to the output folder  
    if not os.path.isabs(options.savestate):
      options.savestate = os.path.abspath(os.path.join(options.runfolder, options.savestate))

# Set up a logger each for a file in the output folder and the console.      
def setup_logging():
  
  global options
  
  os.makedirs(options.runfolder, exist_ok = True)

  fh = logging.FileHandler(options.runfolder + '\\FridgeIQGenerator.log')
  fh.setLevel(options.log_level_int)

  ch = logging.StreamHandler()
  ch.setLevel(options.log_level_int)

  ch.setFormatter(logging.Formatter('({thread}) [{levelname:7}] {name} - {message}', style='{'))
  fh.setFormatter(logging.Formatter('{asctime} ({thread}) [{levelname:7}] {name} - {message}', style='{'))

  root = logging.getLogger()
  root.addHandler(ch)
  root.addHandler(fh)
  root.setLevel(logging.DEBUG)

  # Silence logging from inside matplotlib
  logging.getLogger('matplotlib').setLevel(logging.INFO)

# Plot a playing field. challengeid is the name for the challenge and built
# from the collection of shards covered. So it will be the same regardless
# of multiple ways to cover them with parts. Solutionid is built from the individual
# placements of parts, so it is unique to the solution itself. Solutionid can be
# passed empty in which case only the gray challenge is plotted. Placements is the
# list of parts as placed to make that solution. This includes their geometry and
# the shards they cover.
def plot(challengeid, solutionid, placements):

  global options
  global challenges_found
  
  logger = logging.getLogger('plot')

  # Build a filename for the frame. All frames go into the current output folder and
  # are prefixed by the fingerprint of the challenge.
  figname = options.runfolder + '\\' + challengeid
  if solutionid:
    if options.saveall:
      # When saving all solutions give the frame a unique name for each
      # solution of the same challenge.
      figname += '-' + solutionid
    else:
      # When saving a single solution give the frame a name that will 
      # collide with any other solution-frame already found.
      figname += '-solution'
  else:
    figname += '-challenge' 
  figname += '.svg'

  # We have made sure that a frames content is uniquely identified by its
  # name on disk. So if it exists there is no point in recreating it.
  if (os.path.isfile(figname)):
    logger.debug("Plot \"{figname}\" exists.".format(figname = os.path.splitext(os.path.basename(figname))[0]))
  else:    
    logger.debug("Creating plot \"{figname}\".".format(figname =  os.path.splitext(os.path.basename(figname))[0]))
    
    fig = pyplot.figure(1, figsize=(5,5), dpi=90)
    ax = fig.add_subplot(1,1,1) # rows, columns, index
    
    # No axes ticks
    ax.yaxis.set_major_locator(pyplot.NullLocator())
    ax.xaxis.set_major_formatter(pyplot.NullFormatter())
    ax.yaxis.set_minor_locator(pyplot.NullLocator())
    ax.xaxis.set_minor_formatter(pyplot.NullFormatter())

    for placement in placements:
      
      if solutionid:
        # If asked to plot a solution draw each part as colored polygon.
        patch = PolygonPatch(placement.polygon, facecolor=placement.part.color, alpha=0.5)
        ax.add_patch(patch)
      else:
        # If asked to plot the challenge (no solutionid passed in), draw all the
        # shards as gray triangles.
        for shard in placement.shards.list:
          patch = PolygonPatch(shard.polygon, facecolor="gray", edgecolor="gray")
          ax.add_patch(patch)

    ax.set_title('FridgeIQ')
    xrange = [-options.horizon-3, options.horizon+3]
    yrange = [-options.horizon-3, options.horizon+3]
    ax.set_xlim(*xrange)
    ax.set_ylim(*yrange)
    ax.set_aspect(1)
    
    # If we are saving a challenge we have found a new one. Celebrate!
    if (not solutionid):
      challenges_found = challenges_found + 1
      if options.playfanfare:
        wav = simpleaudio.WaveObject.from_wave_file(os.path.dirname(os.path.realpath(__file__)) + '\\fanfare.wav')
        wav.play()

    fig.savefig(figname, format = "svg")

    figname = os.path.splitext(figname)[0] + ".png"
    fig.savefig(figname, format = "png")
    
    pyplot.close(fig)

# A simple wrapper for hashing to fingerprint challenges and solutions.   
def hash(string):
  m = hashlib.md5()
  m.update(string.encode("UTF-8"))
  return m.hexdigest()

# Make a list of 
def makesymmetryconstraint(symmetryconstraints, shards, mename, me, othername):
  
  result = None

  # Have we already created exactly this constraint or its symmetric partner? If so skip it.
  if (not (mename + "|" + othername) in symmetryconstraints) and (not (othername + "|" + mename) in symmetryconstraints): 
    # Does the target-shard even exist? It may be outside the horizon.
    if othername in shards:
      if shards[othername].placements:        
        # Create a constraint that says the mename-shard must be covered or uncovered in
        # the same state as the othername shard for this to be a symmetric challenge.
        other = z3.Or([x for x in list(map(lambda placement: placement.x, shards[othername].placements))])
        result = (me == other)
    
    # Remember that we have asserted this constraint already and do not need to create
    # it again. Not even in the other direction.
    symmetryconstraints[mename + "|" + othername] = True
    symmetryconstraints[othername + "|" + mename] = True

  return result

def generate():
  
  global options

  logger = logging.getLogger('generate')

  parts = [p for p in partscatalog if p.name in list(options.partslist)]
  area = sum(map(lambda part: part.polygon.area, parts)) 
  logger.info('Generating challenges_found for {partcount} parts ({partslist}) with total area {area} on a horizon of {horizon} ({n}x{n} units).'.format(
    partcount = len(parts),
    partslist = options.partslist,
    area = area,
    horizon = options.horizon,
    n = 2*options.horizon)
  )

  # Set up a Z3 solver to accept constraints
  z3.set_param('parallel.enable', options.z3_parallel)
  solver = z3.Solver()

  # Generate a list of all the shards that make up the square between -horizon and +horizon
  # in x- and y-direction.
  logger.debug('Splitting board into shards.')
    
  shards = {}
  for xoffset in range(-options.horizon, options.horizon + 1):
    for yoffset in range(-options.horizon, options.horizon + 1):
      for direction in list("news"):
        shard = Shard(xoffset, yoffset, direction)
        shards[shard.name] = shard
  logger.debug('Split board into {n} shards.'.format(n=len(shards)))
    
  # For each part generate all possible placements and a boolean variable for each. These we 
  # call by the name of the part with indexes for the x and y offset and the degrees of rotation.
  for part in parts:
    
    logger.debug('Placing part {name}.'.format(name=part.name))
      
    for rotation in part.rotations:
      # Rotate in place
      rotatedpoly = rotate(part.polygon, rotation, Point(0, 0))
    
      # Figure out the part bounds in that orientation. This will not change
      # during the scan.
      partbounds = rotatedpoly.bounds
      partwidth = partbounds[2]-partbounds[0]
      partheight = partbounds[3]-partbounds[1]
            
      # Scan two-dimensionally over the horizon.
      for xoffset in range(-options.horizon - int(math.ceil(partbounds[0])), options.horizon - int(math.ceil(partbounds[0])) - int(math.ceil(partwidth)) + 1):
        for yoffset in range(-options.horizon - int(math.ceil(partbounds[1])), options.horizon - int(math.ceil(partbounds[1])) - int(math.ceil(partheight)) + 1):
          # Put a polygon in this position.
          finalpoly = translate(rotatedpoly, xoffset, yoffset)

          # Create a placement, which internally creates the Z3 boolean 
          # and put it into the list of placements for this part.
          placement = Placement(part, finalpoly, rotation, xoffset, yoffset)
          part.placements.append(placement)
          
          # Attach this placement to the list of placements of each shard
          # the part covers at that placement.
          for shard in placement.shards.list:
            shards[shard.name].placements.append(placement)

    logger.debug('Placed part {name} in {n} positions.'.format(name=part.name, n=len(part.placements)))

    # Add a constraint that we want each part to appear in exactly one of
    # the placements we determined.
    solver.add( z3.PbEq([(x,1) for x in list(map(lambda placement: placement.x, part.placements))], 1) )

  # For each shard add a constraint that we want it to be covered by zero or one of the
  # parts. This removes overlap.
  logger.debug('Generating constraints to avoid overlap.')
  for shard in shards.values():
    solver.add( z3.PbLe([(x,1) for x in list(map(lambda placement: placement.x, shard.placements))], 1) ) 

  # Symmetry. For each shard add a constraint that its coverage must be the same as that
  # of all its symmetry-partners.
  #
  # We do this twice because we can have two kinds of challenges. Those with even symmetry have
  # bounding boxes of even side-length and the square (0,0) sits to the right of the 
  # north-south-symmetry axis and on top of the east-west-axis. Those with odd symmetry have
  # these axes passing through the middle of the (0,0)-square. 
  symmetryconstraints_even = {}
  symmetryconstraints_odd = {}

  oddconstraints = []
  evenconstraints = []

  logger.debug('Generating constraints for even symmetry.')
  for shard in shards.values():
    if (shard.xoffset >= 0) and (shard.yoffset >= 0): 
      me = z3.Or([x for x in list(map(lambda placement: placement.x, shard.placements))])
      
      if options.evensize:        
        mirror_e_w_even_name = Shard.mirror_e_w_even(shard)
        con = makesymmetryconstraint(symmetryconstraints_even, shards, shard.name, me, mirror_e_w_even_name)
        if (con != None):
          evenconstraints.append(con)

        mirror_n_s_even_name = Shard.mirror_n_s_even(shard)
        con = makesymmetryconstraint(symmetryconstraints_even, shards, shard.name, me, mirror_n_s_even_name)
        if (con != None):
          evenconstraints.append(con)

        mirror_sw_ne_even_name = Shard.mirror_sw_ne_even(shard)
        con = makesymmetryconstraint(symmetryconstraints_even, shards, shard.name, me, mirror_sw_ne_even_name)
        if (con != None):
          evenconstraints.append(con)

        mirror_nw_se_evenname = Shard.mirror_nw_se_even(shard)
        con = makesymmetryconstraint(symmetryconstraints_even, shards, shard.name, me, mirror_nw_se_evenname)
        if (con != None):
          evenconstraints.append(con)

  logger.debug('Generating constraints for odd symmetry.')
  for shard in shards.values():
    if (shard.xoffset >= 0) and (shard.yoffset >= 0): 
      me = z3.Or([x for x in list(map(lambda placement: placement.x, shard.placements))])
  
      if options.oddsize:      
        mirror_e_w_oddname = Shard.mirror_e_w_odd(shard)
        con = makesymmetryconstraint(symmetryconstraints_odd, shards, shard.name, me, mirror_e_w_oddname)
        if (con != None):
          oddconstraints.append(con)

        mirror_n_s_oddname = Shard.mirror_n_s_odd(shard)
        con = makesymmetryconstraint(symmetryconstraints_odd, shards, shard.name, me, mirror_n_s_oddname)
        if (con != None):
          oddconstraints.append(con)

        mirror_sw_ne_oddname = Shard.mirror_sw_ne_odd(shard)
        con = makesymmetryconstraint(symmetryconstraints_odd, shards, shard.name, me, mirror_sw_ne_oddname)
        if (con != None):
          oddconstraints.append(con)

        mirror_nw_se_oddname = Shard.mirror_nw_se_odd(shard)
        con = makesymmetryconstraint(symmetryconstraints_odd, shards, shard.name, me, mirror_nw_se_oddname)
        if (con != None):
          oddconstraints.append(con)

  if options.evensize and options.oddsize:
    even = z3.And(evenconstraints)
    odd = z3.And(oddconstraints)
    even_or_odd = z3.Or(even, odd)
    solver.add(even_or_odd)
  elif options.evensize:
    solver.add(z3.And(evenconstraints))
  elif options.oddsize:
    solver.add(z3.And(oddconstraints))
  
  # If we have a save-state file we ignore all of the above and use whatever is in there.
  # Hopefully this restarts the solving at the last point we saved it. Which is just
  # after we add a fresh blocking clause.
  # Caution: This ignores all other commandline settings so only do it if you are certain
  # that you are actually running the same problem!
  if options.savestate:
    if (os.path.isfile(options.savestate)):
      logger.warn('Reading saved state from "{savestate}"'.format(savestate = options.savestate))
      solver.reset()
      solver.from_file(options.savestate)
      
  # Now let the solver loose
  logger.info('Executing solver.')
  verdict = solver.check()
  logger.debug('Solver verdict is: "{verdict}".'.format(verdict = verdict))
  
  solutions = 0

  while verdict == z3.sat:
    # Found a solution!
    solutions += 1
    logger.info('Solution #{solution}.'.format(solution = solutions))
          
    # Interpret model and produce output
    model = solver.model()

    # Find a list of the placements that evaluate to true in the model,
    # this is where the parts actually go in this solution.
    #
    # Build a canonical name for this pattern. To do this collect the names of all
    # the shards covered by tiles. Sort that, concatenate into a long string and
    # MD5-hash it. This becomes a fingerprint-name that identfies the pattern.
    # We do a similar thing for the placements and get another MD5 sum. We then
    # plot the pattern and the solution.
    trueplacements = []
    trueplacementnames = []
    trueshardnames = []

    for part in parts:
      for placement in part.placements:
        if model[placement.x]:
          #logger.debug('  {xname}=True: Part {name} goes to ({xoffset},{yoffset}) at {rotation} degrees.'.format(
          #  xname = placement.xname,
          #  name = part.name, 
          #  xoffset = placement.xoffset,
          #  yoffset = placement.yoffset,
          #  rotation = placement.rotation
          #))
          trueplacements.append(placement)
          trueplacementnames.append(placement.xname)
          for shard in placement.shards.list:
            trueshardnames.append(shard.name)

          break # There can be only one placement evaluating to true per part.

    trueshardnames.sort()
    challengeid = hash("|".join(trueshardnames))
    
    trueplacementnames.sort()
    solutionid = hash("|".join(trueplacementnames))

    # Plot the challenge and then plot the solution which may be different.
    # Within plot() there is code that finally decides on a filename and wether
    # it needs to be generated or not. 
    plot(challengeid, "", trueplacements)
    plot(challengeid, solutionid, trueplacements)

    # Add a blocking clause for this model so we can look for the next solution.
    logger.debug('Add blocking clause for specific placement.')
    blockingclause = z3.Not(z3.And([ p.x for p in trueplacements ]))
    logger.debug('Blocking clause:\n{blockingclause}'.format(blockingclause = blockingclause))
    solver.add(blockingclause)

    # The blocking clause above will generate either a new challenge or
    # a new solution to a known challenge. If we are not interested in all
    # solutions we can create a blocking clause that excludes any solution
    # resulting in the same shape.
    # To do we need to OR all placements that include one of the trueshards
    # and NOT AND them. 
    if not options.saveall:
      logger.debug('Add blocking clause for specific challenge.')

      shardconstraints = []
      for shardname in trueshardnames:
        # Find all the placements that include this shard.
        shard = shards[shardname]
        # For this shard to be covered means the OR of all the placements on it is true
        shardconstraints.append(z3.Or([ p.x for p in shard.placements ]))

      # For the same shape to be produced all of these must be true, but we want
      # the opposite.
      blockingclause = z3.Not(z3.And(shardconstraints))
      logger.debug('Blocking clause:\n{blockingclause}'.format(blockingclause = blockingclause))
      solver.add(blockingclause)
      
    # If asked for it save the state of the solver now.
    if options.savestate:
      logger.debug('Save new solver state.')
      smt2 = solver.sexpr()
      with open(options.savestate, mode='w', encoding='ascii') as f: # overwrite
        f.write(smt2)
        f.close()

    # Recheck to get another.
    logger.debug('Executing solver.')
    verdict = solver.check()
    logger.debug('Solver verdict is: "{verdict}".'.format(verdict = verdict))
  
def main():
  
  global options
  global challenges_found
  
  parse_commandline()
  setup_logging()

  logger = logging.getLogger('main')
  logger.info('Starting. Output goes to {runfolder}'.format(runfolder=options.runfolder))

  # Hardcoded settings for debugging overriding the commandline:
  
  #options.savestate = 'C:\\Users\\Marian Aldenhövel\\Desktop\\FridgeIQ\\src\savestate.smt2'

  # Even square:
  #options.horizon = 3
  #options.partslist = 'AIJMOQS'

  # Odd square
  #options.horizon = 3
  #options.partslist = 'IJMR'

  # Odd square
  #options.horizon = 3
  #options.partslist = 'ABDEIMNYRST'

  #z3.set_option('auto_config', False)
  #z3.set_option('smt.phase_selection',5)

  # Call the generator
  generate()
  
  endtime = datetime.datetime.now().replace(microsecond=0)
  runtime = (endtime-starttime)
  logger.info('Finished. Found {challenges_found} different challenges. Total runtime: {runtime}'.format(challenges_found=challenges_found, runtime=runtime))

# Poor man's unit tests
def tests():
  
  logger = logging.getLogger('tests')

  shard = Shard(1, 3, "n") # (1)-(3)-n
  assert Shard.mirror_e_w_even(shard) == '(-2)-(3)-n'
  assert Shard.mirror_n_s_even(shard) == '(1)-(-4)-s'
  assert Shard.mirror_nw_se_even(shard) == '(-4)-(-2)-w'
  assert Shard.mirror_sw_ne_even(shard) == '(3)-(1)-e'

  shard = Shard(1, 1, "n") # (1)-(1)-n
  assert Shard.mirror_e_w_even(shard) == '(-2)-(1)-n'
  assert Shard.mirror_n_s_even(shard) == '(1)-(-2)-s'
  assert Shard.mirror_nw_se_even(shard) == '(-2)-(-2)-w'
  assert Shard.mirror_sw_ne_even(shard) == '(1)-(1)-e'

  shard = Shard(1, 1, "e") # (1)-(1)-e
  assert Shard.mirror_e_w_even(shard) == '(-2)-(1)-w'
  assert Shard.mirror_n_s_even(shard) == '(1)-(-2)-e'
  assert Shard.mirror_nw_se_even(shard) == '(-2)-(-2)-s'
  assert Shard.mirror_sw_ne_even(shard) == '(1)-(1)-n'

  shard = Shard(1, 1, "w") # (1)-(1)-w
  assert Shard.mirror_e_w_even(shard) == '(-2)-(1)-e'
  assert Shard.mirror_n_s_even(shard) == '(1)-(-2)-w'
  assert Shard.mirror_nw_se_even(shard) == '(-2)-(-2)-n'
  assert Shard.mirror_sw_ne_even(shard) == '(1)-(1)-s'

  shard = Shard(1, 1, "s") # (1)-(1)-s
  assert Shard.mirror_e_w_even(shard) == '(-2)-(1)-s'
  assert Shard.mirror_n_s_even(shard) == '(1)-(-2)-n'
  assert Shard.mirror_nw_se_even(shard) == '(-2)-(-2)-e'
  assert Shard.mirror_sw_ne_even(shard) == '(1)-(1)-w'

  shard = Shard(1, 2, "n") # (1)-(2)-n
  assert Shard.mirror_e_w_odd(shard) == '(-1)-(2)-n'
  assert Shard.mirror_n_s_odd(shard) == '(1)-(-2)-s'
  assert Shard.mirror_nw_se_odd(shard) == '(-2)-(-1)-w'
  assert Shard.mirror_sw_ne_odd(shard) == '(2)-(1)-e'
  
  logger.debug('All unit tests passed.')

if __name__ == '__main__':
  #tests()
  main()