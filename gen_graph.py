#!/usr/bin/env python3

import os

def save(fn, z):
    d = open(fn, 'w', encoding="utf-8")
    d.write(z)
    d.close()

def main():

    # MAIN
    list_parse = []
    dirs = ['Gen', 'Libs', 'ListsOp', 'Low', 'Mid']
    for dir in dirs:
        coqfiles = os.listdir(dir)
        for coqfile in coqfiles:
            if coqfile[-2:] == '.v':
                list_parse.append(dir + '.' + coqfile[:-2])

    requires = ''
    prints = 'Print FileDependGraph \n'
    for cq in list_parse:
        requires += 'Require Import Tweetnacl.'+ cq + '.\n'
        prints += '\t' + cq + '\n'

    output = requires + '\n'
    output += 'Require dpdgraph.dpdgraph.\n'
    output += 'Set DependGraph File "graph.dpd".\n'
    output += prints + '.\n'
    # print(list_parse)
    print(output)
    save('gen_graph_main.v', output)


    # High
    list_parse = []
    dirs = ['High']
    for dir in dirs:
        coqfiles = os.listdir(dir)
        for coqfile in coqfiles:
            if coqfile[-2:] == '.v':
                list_parse.append(dir + '.' + coqfile[:-2])
    requires = ''
    prints = 'Print FileDependGraph \n'
    for cq in list_parse:
        requires += 'Require Import Tweetnacl.'+ cq + '.\n'
        prints += '\t' + cq + '\n'

    output = requires + '\n'
    output += 'Require dpdgraph.dpdgraph.\n'
    output += 'Set DependGraph File "graph.dpd".\n'
    output += prints + '.\n'
    # print(list_parse)
    print(output)
    save('gen_graph_high.v', output)


if __name__ == '__main__':
    main()
