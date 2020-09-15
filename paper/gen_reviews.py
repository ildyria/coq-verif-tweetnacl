#!/usr/bin/env python3

import os
import glob
import argparse
from string import Template



def save(fn, z):
    # print(z)
    d = open(fn, 'w', encoding="utf-8")
    d.write(z)
    d.close()

def read(fn):
    data = ''
    with open(fn, 'r', encoding="utf-8") as file:
        data = file.read()
    return data



def is_tex(fn):
    return fn[-4:] == '.tex'

def is_ignored(fn):
    return fn[0:1] == '_'
def is_appendix(fn):
    return fn[0:1] == 'A'



def is_not_tex(s):
    return s != '' and s[-4:] != '.tex'

def is_not_tikz(s):
    return "tikz/" not in s

def check_tex(s):
    if is_not_tex(s):
        msg = "%r is not a .tex" % s
        raise argparse.ArgumentTypeError(msg)
    return s




def parse_arguments():
    parser = argparse.ArgumentParser(description='Generate paper.')
    parser.add_argument('input', nargs=1, default='', help='input: paper.tex', type=check_tex)
    args = parser.parse_args()

    return args.input[0]

def main():

    fn = parse_arguments()

    files = [x for x in glob.glob("_reviews/*.tex", recursive=True) if is_tex(x) and not (x == fn) and is_not_tikz(x)]

    # for f in files:
    #     print(f)

    files.sort()

    main_output = ''
    for f in files:
        main_output += "\\input{{{}}}\n".format(f)

    appendix_output = ''

    output = read('_tpl' + fn)
    output = output.replace('\\intput{main}\n', '$main_output')
    output = Template(output)
    output = output.safe_substitute(main_output = main_output, appendix_output = appendix_output)
    # print(output)

    save(fn, output)

main()