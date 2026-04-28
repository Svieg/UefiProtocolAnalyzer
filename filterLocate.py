import re
import sys

pattern = re.compile(r"/(([A-Za-z])+Dxe)/.*&([A-Za-z]+Guid)")

with open(sys.argv[1]) as f:
    for line in f:
        match = pattern.search(line)
        if match:
            print(f"{match.group(1)},{match.group(3)}")
