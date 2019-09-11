#!/usr/bin/env python3

import os
import argparse



def save(fn, z):
    # print(z)
    d = open(fn, 'w', encoding="utf-8")
    d.write(z)
    d.close()

def read(fn):
    data = '';
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

    files = [x for x in os.listdir('.') if not is_ignored(x) and is_tex(x) and not (x == fn)]

    appendices = [x for x in files if is_tex(x) and is_appendix(x)]
    main = [x for x in files if x not in appendices]

    main.sort()
    appendices.sort()

    output = read('_head.tex')
    output += "\n"

    for f in main:
        output += "\\input{{{}}}\n".format(f)

    output += "\n"
    output += "\\vspace*{1cm}\n"
    output += "{\\footnotesize \\bibliographystyle{IEEEtran}\n"
    output += "\\bibliography{collection}}\n"
    output += "\n"
    output += "\\begin{appendix}\n"

    for f in appendices:
        output += "  \\input{{{}}}\n".format(f)


    output += "\\end{appendix}\n"
    output += "\n"
    output += "\\end{document}\n"

    # print(output)
    save(fn, output)

main()
