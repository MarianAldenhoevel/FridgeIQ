import re

line = "2019-03-14 09:45:50,087 (11712) [DEBUG  ] plot - Plot \"9d6b8a845b3711389019501a27dff648-challenge\" exists."
plotnamepattern = re.compile("Plot \"([0-9A-Fa-f]{32})-")

print(line)
print(plotnamepattern.pattern)
match = plotnamepattern.search(line)
print(match)  
print(match.group(1))