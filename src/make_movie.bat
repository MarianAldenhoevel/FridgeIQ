rmdir /S /Q .\movie
del movie.mp4
python .\FridgeIQ.py --puzzle triangle_03 --decorate-frames False -pc True -pd True -ps True -pb True --play-fanfare False -of .\movie
ffmpeg -framerate 4 -i movie\%%05d.png movie.mp4