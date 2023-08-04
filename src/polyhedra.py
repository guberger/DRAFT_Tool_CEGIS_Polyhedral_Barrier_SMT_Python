import numpy as np

class AffForm:
    def __init__(self, a, beta):
        self.a = a
        self.beta = beta

    def __repr__(self):
        return "AffForm %s %s" % (self.a, self.beta)

    def eval(self, x):
        return np.dot(self.a, x) + self.beta
    
class Polyhedron:
    def __init__(self, afs):
        self.afs = afs
    
    def __repr__(self):
        return "Polyhedron %s" % self.afs
    
    def eval(self, x):
        return max(af.eval(x) for af in self.afs)
    
class Region:
    def __init__(self, ps):
        self.ps = ps

    def __repr__(self):
        return "Region %s" % self.ps
    
    def eval(self, x):
        return min(p.eval(x) for p in self.ps)