import numpy as np
import z3
from .polyhedra import AffForm

class Generator:
    def __init__(self, dim, naf, eps, betamax):
        self.dim = dim
        self.naf = naf
        self.eps = eps
        self.betamax = betamax
        self.xs_inside = []
        self.xys_transition = []
        self.xs_outside = []

    def find_candidate(self):
        ctx = z3.Context()
        solver = z3.Solver(ctx=ctx)
        afs = [AffForm(
            np.array([
                z3.Real("a" + str(k) + "[" + str(i) + "]", ctx=ctx)
                for i in range(self.dim)
            ]),
            z3.Real("b" + str(k), ctx=ctx)
        ) for k in range(self.naf)]
        
        for af in afs:
            for ai in af.a:
                solver.add(ai <= +1)
                solver.add(ai >= -1)
            solver.add(af.beta <= +self.betamax)
            solver.add(af.beta >= -self.betamax)
            
        for x in self.xs_inside:
            for af in afs:
                solver.add(af.eval(x) <= -self.eps)
            
        for x in self.xs_outside:
            cons = []
            for af in afs:
                cons.append(af.eval(x) >= +self.eps)
            solver.add(z3.Or(cons))

        for (x, y) in self.xys_transition:
            cons_x = []
            cons_y = []
            for af in afs:
                cons_x.append(af.eval(x) <= +self.eps)
                cons_y.append(af.eval(y) <= -self.eps)
            solver.add(z3.Implies(z3.And(cons_x), z3.And(cons_y)))

        res = solver.check()
        if res == z3.sat:
            model = solver.model()
            afs_opt = [AffForm(
                np.array([float(model[ai].as_fraction()) for ai in af.a]),
                float(model[af.beta].as_fraction())
            ) for af in afs]
            return True, afs_opt
        else:
            return False, None