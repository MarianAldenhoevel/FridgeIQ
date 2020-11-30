# -*- coding: utf-8 -*-
'''
@author: Marian Aldenhövel <marian.aldenhoevel@marian-aldenhoevel.de>
'''

# This is a program to build a booklet in PDF format from all the challenge- and
# solution plots dropped into a folder by a FridgeIQ-generator program.

import logging
import os
import sys
import argparse
import tempfile
import svglib.svglib
import PIL

from reportlab.pdfgen import canvas
from reportlab.graphics import renderPM
from reportlab.lib.units import mm
from reportlab.pdfbase.pdfmetrics import stringWidth

# Global variables
options = None
  
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
    
    parser = argparse.ArgumentParser(
        description = 'Create a PDF-booklet from the output of the FridgeIQGenerator.', 
    )

    parser.add_argument('-ll', '--log-level',
        action = 'store',
        default = 'DEBUG',
        help ='Set the logging output level to CRITICAL, ERROR, WARNING, INFO or DEBUG (default: %(default)s)',
        dest ='log_level',
        metavar = 'level'
    )

    parser.add_argument('-fo', '--folder',
        #required = True,
        action = 'store',
        default = '',
        help = 'FridgeIQGenerator output-folder',
        dest = 'folder',
        metavar = 'folder'
    )

    options = parser.parse_args()
    options.log_level_int = getattr(logging, options.log_level, logging.INFO)

# Set up a logger each for a file in the output folder and the console.      
def setup_logging():
  
    global options
  
    os.makedirs(options.folder, exist_ok = True)

    fh = logging.FileHandler(options.folder + '\\Booklet.log')
    fh.setLevel(options.log_level_int)

    ch = logging.StreamHandler()
    ch.setLevel(options.log_level_int)

    ch.setFormatter(logging.Formatter('({thread}) [{levelname:7}] {name} - {message}', style='{'))
    fh.setFormatter(logging.Formatter('{asctime} ({thread}) [{levelname:7}] {name} - {message}', style='{'))

    root = logging.getLogger()
    root.addHandler(ch)
    root.addHandler(fh)
    root.setLevel(logging.DEBUG)

    # Silence logging from inside libraries
    logging.getLogger('svglib').setLevel(logging.INFO)
    logging.getLogger('PIL').setLevel(logging.INFO)

class Booklet():

    logger = logging.getLogger('Booklet') 

    PAGEWIDTH = 200*mm
    PAGEHEIGHT = 200*mm
    MARGIN = 10*mm
    CROP_PERCENT = 17/100.0

    # Scale a reportlab.graphics.shapes.Drawing() object while maintaining the aspect ratio
    def scale(self, drawing, scaling_factor):
        drawing.width = drawing.width * scaling_factor
        drawing.height = drawing.height * scaling_factor
        drawing.scale(scaling_factor, scaling_factor)
        
        return drawing

    # Convert a svg file to pixels and put that image on the current page.
    def addplot(self, svgfilename):
        
        # Turn SVG into a Reportlab drawing of a convenient size.
        drawing = svglib.svglib.svg2rlg(svgfilename)
        self.scale(drawing, 3)

        # Render the Reportlab drawing as PNG to disk.
        temp = tempfile.mkstemp(suffix = '.png', prefix = 'makebooklet_')
        try:
            os.close(temp[0])
            renderPM.drawToFile(drawing, temp[1], fmt='PNG')        
            
            # Crop the image to remove all the crud around the image itself.
            pil = PIL.Image.open(temp[1])
            width, height = pil.size   # Get dimensions
            left = width * self.CROP_PERCENT
            top = height * self.CROP_PERCENT
            right = width - left
            bottom = height- top
            pil = pil.crop((left, top, right, bottom))
            pil.save(temp[1])
        
            self.canvas.drawImage(
                temp[1], 
                x = self.MARGIN, 
                y = self.MARGIN, 
                width = self.PAGEWIDTH - 2 * self.MARGIN, 
                height = self.PAGEHEIGHT -2 * self.MARGIN, 
                preserveAspectRatio=True, 
                anchor = 'c',
                mask='auto')          
        finally:
            os.remove(temp[1])

    def addpagetitle(self, title):        
        fontname = "Helvetica"
        fontsize = 20
        width = stringWidth(title, fontname, fontsize)

        text = self.canvas.beginText((self.PAGEWIDTH - width) / 2.0, self.PAGEHEIGHT - 10*mm)
        text.setFont(fontname, fontsize)
        text.textLine(title)

        self.canvas.drawText(text)

        y = self.PAGEHEIGHT - 15*mm 
        self.canvas.line(0, y, self.PAGEWIDTH, y)
                
    def pagenum(self):
        return self.canvas.getPageNumber()

    def addpagenum(self):        
        s = "{page}".format(page = self.pagenum())
        
        fontname = "Helvetica"
        fontsize = 12
        width = stringWidth(s, fontname, fontsize)

        text = self.canvas.beginText((self.PAGEWIDTH - width) / 2.0, 6*mm)
        text.setFont(fontname, fontsize)
        text.textLine(s)

        self.canvas.drawText(text)

        y = 15*mm 
        self.canvas.line(0, y, self.PAGEWIDTH, y)
        
    def save(self):
        self.canvas.save()

    def showpage(self):
        self.canvas.showPage()

    def addchallenge(self, challengeid):

        global options

        self.logger.info('Add challenge {challengeid}'.format(challengeid = challengeid))

        # Add a page for the challenge.
        challengefilename = os.path.join(options.folder, challengeid + '-challenge.svg')
        self.logger.debug('Add challenge from "{challengefilename}"'.format(challengefilename = challengefilename))
        
        self.canvas.setFillGray(0.5)
        self.canvas.setStrokeGray(0.5)
        self.addplot(challengefilename)
        self.addpagenum()
        self.addpagetitle(challengeid)
        self.showpage()

        # And one each for every solution we can find in the output folder. 
        solutions = [f for f in os.listdir(options.folder) if (os.path.isfile(os.path.join(options.folder, f)) and f.startswith(challengeid) and f.endswith('.svg') and (not f.endswith('-challenge.svg')))]
        for solution in solutions:
            solutionfilename = os.path.join(options.folder, solution)
            self.logger.debug('Add solution from "{solutionfilename}"'.format(solutionfilename = solutionfilename))
            
            self.canvas.setFillGray(0.5)
            self.canvas.setStrokeGray(0.5)
            self.addplot(solutionfilename)
            self.addpagenum()
            self.addpagetitle(challengeid)
            self.showpage()
            
        # If we have an even number of solutions add a blank page so we start each challenge 
        # on the same facing page.
        if (len(solutions) % 2 == 0):
            self.showpage()    

    def __init__(self, filename):
        self.canvas = canvas.Canvas(filename)
        self.canvas.setPageSize((self.PAGEWIDTH, self.PAGEHEIGHT))
        
        self.canvas.setTitle('FridgeIQ')
        self.canvas.setAuthor('Marian Aldenhövel')
        self.canvas.setSubject('FridgeIQ Snowflake Challenges')
        self.canvas.setCreator('FridgeIQGenerator')
        self.canvas.setKeywords('FridgeIQ Puzzle')
        
def main():
  
    global options

    parse_commandline()

    # override commandline for testing
    options.folder = 'C:\\Users\\Marian Aldenhövel\\Desktop\\FridgeIQ\\src\\generate_all'

    setup_logging()

    logger = logging.getLogger('main')
    logger.info('Creating booklet from data found in "{folder}".'.format(folder=options.folder))
  
    filename = os.path.join(options.folder, 'Booklet.pdf')
    booklet = Booklet(filename)

    challenges = list(set(map(lambda filename: filename.split('-', 2)[0], [f for f in os.listdir(options.folder) if (os.path.isfile(os.path.join(options.folder, f)) and f.endswith('-challenge.svg'))])))
    challenges.sort()
    logger.debug('Found {n} unique challenges.'.format(n = len(challenges)))
    
    for challenge in challenges:
        booklet.addchallenge(challenge)

    booklet.save()
    logger.info('Booklet with {pagenum} pages saved to "{filename}".'.format(pagenum = booklet.pagenum()-1, filename = filename))

    logger.info('Finished.')

if __name__ == '__main__':
    main()