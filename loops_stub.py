#!/usr/bin/env python3
# File:  stub.py
# Author:  mikolas
# Created on:  Sat Oct 12 10:30:54 WEST 2019
# Copyright (C) 2019, Mikolas Janota
import sys,subprocess 
from itertools import combinations

solver = './cryptominisat5'

def neg(l): return l[1:] if l[0] == '-' else '-'+l
def var(l): return l[1:] if l[0] == '-' else l
def sign(l): return l[0] == '-'

class Enc:
    def __init__(self, input_count,  node_count):
         self.node_count = node_count
         self.input_count = input_count
         self.constraints = []
         self.fresh = 0

    def x(self,i): return 'x_{}'.format(i)
    def y(self,i): return 'y_{}'.format(i)
    def v(self,i): return 'v_{}'.format(i)
    def l(self,i,j): return 'l_{}_{}'.format(i,j)
    def r(self,i,j): return 'r_{}_{}'.format(i,j)
    def p(self,j,i): return 'p_{}_{}'.format(i,j)
    def a(self,r,j): return 'a_{}_{}'.format(r,j)
    def u(self,r,j): return 'u_{}_{}'.format(r,j)
    def c(self,j): return 'c_{}'.format(j)
    def d0(self,r,j): return 'd0_{}_{}'.format(r,j)
    def d1(self,r,j): return 'd1_{}_{}'.format(r,j)
    def d(self,n,r,j):
        if n == 0:
            return self.d0(r,j)
        elif n == 1:
            return self.d1(r,j)
        else:
            return ("Wrong feature value!!!!!")
  
	
    

    def add_constraint(self, constraint):
        '''add constraints, which is a list of literals'''
        self.constraints.append(constraint)

    def mk_fresh(self, nm):
        '''make fresh variable'''
        self.fresh = self.fresh + 1
        return '_' + nm + '__' + str(self.fresh)

    def mk_and(self, l1, l2):
        '''encode and between l1 and l2 by introducing a fresh variable'''
        r = self.mk_fresh(l1+'_and_'+l2)
        self.constraints.append([neg(l1), neg(l2), r])
        self.constraints.append([l1, neg(r)])
        self.constraints.append([l2, neg(r)])
        return r

    def add_iff(self, l1, l2):
        '''add iff constraint between l1 and l2'''
        self.constraints.append([neg(l1), l2])
        self.constraints.append([l1, neg(l2)])
        
    def add_atmost_one(self,l):
        '''add constrains to satisfy at most one for list l'''
        for x,y in combinations(l,2):
            self.add_constraint([neg(x),neg(y)])
        


    def print_model(self,model):
        '''prints SAT model, eventually should print the decision tree'''
        print('# === model')
        for str_var in sorted(self.var_map.keys()):
            v = self.var_map[str_var]
            val = '?'
            if v in model and model[v]: val='T'
            if v in model and not model[v]: val='F'
            print('# {}={} ({})'.format(str_var,val,v))
        print('# === end of model')
        print('# === tree (TODO)')
        print('# === end of tree')


    def mk_cnf(self,print_comments):
        '''encode constraints as CNF in DIMACS'''
        maxid = 0
        self.var_map = dict()
        cs = 0
        rv = ''
        for c in self.constraints:
            if not isinstance(c, list): continue
            cs = cs + 1
            for l in c:
                if var(l) not in self.var_map:
                    maxid = maxid + 1
                    self.var_map[var(l)] = maxid

        rv += 'p cnf {} {}'.format(len(self.var_map), cs) + '\n'
        for c in self.constraints:
            if isinstance(c, list):
                if print_comments:
                    rv += 'c ' + str(c) + '\n'
                rv += ' '.join(map(str,[ -(self.var_map[var(l)]) if sign(l) else self.var_map[l] for l in c])) + ' 0\n'
            else:
                if print_comments:
                    rv += 'c ' + str(c) + '\n'

        return rv

    def enc(self, samples):
        '''encode the problem'''
        def LR(i):
            return [j for j in range(i+1,min(2*i,self.node_count-1)+1) if j%2 == 0]
        def RR(i):
            return [j for j in range(i+2,min(2*i+1,self.node_count)+1) if j%2 == 1]

        #Constrains for binary tree
        #(1)
        self.add_constraint([neg(self.v(1))])
        
        #(2)
        for i in range(1,self.node_count+1):
            for j in LR(i):
                self.add_constraint([neg(self.v(i)),neg(self.l(i,j))])
                
		#(3)
        for i in range(1,self.node_count+1):
            for j in LR(i):  
                self.add_iff(self.l(i,j),self.r(i,j+1))
                    
        #(4)  
        for i in range(1,self.node_count+1):  
            self.add_atmost_one([self.l(i,j) for j in LR(i)])
            self.add_constraint([self.l(i,j) for j in LR(i)]+[self.v(i)])
        
        #(5)
        for i in range(1,self.node_count+1):
            for j in LR(i):    
                self.add_iff(self.p(i,j),self.l(i,j))
            for j in RR(i):
                self.add_iff(self.p(i,j),self.r(i,j))
                
        #(6)
        for j in range(2,self.node_count+1):
            P = [self.p(i,j) for i in range(int(j/2),min(j-1,self.node_count)+1)]
            self.add_atmost_one(P)
            self.add_constraint(P)
		

                
        #Constrains for features
		#index of feature is denoted with "k"

		#(7)
        for k in range(1,self.input_count+1):
            self.add_constraint([neg(self.d0(k,1))])
            for j in range(2,self.node_count+1):
                list_j = []
                for i in range(int(j/2),j): #right implicaton
                    list_j.append(self.mk_and(self.p(i,j),self.d0(k,i))) 
                    list_j.append(self.mk_and(self.a(k,i),self.r(i,j)))
                self.add_constraint([neg(self.d0(k,i))]+list_j)
                
                for i in range(int(j/2),j): #left implication 
                    self.add_constraint([neg(self.p(i,j)),neg(self.d0(k,i)),self.d0(k,j)])
                    self.add_constraint([neg(self.a(k,i)),neg(self.r(i,j)),self.d0(k,j)])
        
        #(8)
        for k in range(1,self.input_count+1):
            self.add_constraint([neg(self.d1(k,1))])
            for j in range(2,self.node_count+1):
                list_j = []
                for i in range(int(j/2),j): #right implicaton
                    list_j.append(self.mk_and(self.p(i,j),self.d1(k,i))) 
                    list_j.append(self.mk_and(self.a(k,i),self.l(i,j)))
                self.add_constraint([neg(self.d1(k,i))]+list_j)
                
                for i in range(int(j/2),j): #left implication 
                    self.add_constraint([neg(self.p(i,j)),neg(self.d1(k,i)),self.d1(k,j)])
                    self.add_constraint([neg(self.a(k,i)),neg(self.l(i,j)),self.d1(k,j)])
        
        
#        # -x1 | -x2
#        self.add_constraint([neg(self.x(1)), neg(self.x(2))])
#        # x1 | x2
#        self.add_constraint([self.x(1), self.x(2)])
#        # x1 <=> x2
#        self.add_iff(self.x(3), self.x(4))
#        # y1 | (y2 & y3)
#        self.add_constraint([self.y(1), self.mk_and(self.y(2),self.y(3))])
#        # -y1
#        self.add_constraint([neg(self.y(1))])
#        
        
def get_model(lns):
    vals=dict()
    found=False
    for l in lns:
        l=l.rstrip()
        if not l: continue
        if not l.startswith('v ') and not l.startswith('V '): continue
        found=True
        vs = l.split()[1:]
        for v in vs:
            if v == '0': break
            vals[int(var(v))] = not sign(v)
    return vals if found else None

def parse(f):
    nms = None
    samples = []
    for l in f:
        s = l.rstrip().split()
        if not s: continue
        if nms:
            samples.append([int(l) for l in s])
        else:
            nms = [int(l) for l in s]
    return (nms, samples)



if __name__ == "__main__":
    debug_solver = False 

    print("# reading from stdin")
    nms, samples = parse(sys.stdin)
    print("# encoding")
    e = Enc(nms[0], nms[1])
    e.enc(samples)
    print("# encoded constraints")
    print("# " + "\n# ".join(map(str, e.constraints)))
    print("# END encoded constraints")
    print("# sending to solver '" + solver + "'")
    cnf = e.mk_cnf(False)
    p = subprocess.Popen(solver, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    (po, pe) = p.communicate(input=bytes(cnf, encoding ='utf-8'))
    if debug_solver:
        print('\n'.join(lns), file=sys.stderr)
        print(cnf, file=sys.stderr)
    print("# decoding result from solver")
    rc = p.returncode
    lns = str(po, encoding ='utf-8').splitlines()
    if rc == 10:
        e.print_model(get_model(lns))
    elif rc == 20:
        print("UNSAT")
    else:
        print("ERROR: something went wrong with the solver")
