import random
import os
import sys

def filter_facts(filename, num):
    with open(filename, "r", encoding="utf-8") as file:
        basename, ext = filename.split(".")
        newfile = open(basename+"-"+str(num)+"." + ext, "w", encoding="utf-8")
        lines = file.readlines()
        random.shuffle(lines)
        newfile.writelines(lines[:min(num, len(lines))])
        newfile.close()

if __name__ == "__main__":
    if len(sys.argv) != 3:
        exit(1)
    filename, num = sys.argv[1:]
    filter_facts(filename, int(num))
