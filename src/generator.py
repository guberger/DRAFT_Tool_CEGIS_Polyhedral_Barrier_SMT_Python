import numpy as np
import z3
from .polyhedra import AffForm

class Generator:
    def __init__(self, dim, naf, cmax):
        self.dim = dim
        self.naf = naf
        self.cmax = cmax
        self.xs_inside = []
        self.xys_transition = []
        self.xs_outside = []

    def find_candidate(self):
        ctx = z3.Context()
        solver = z3.Solver(ctx=ctx)
        afs = [AffForm(
            np.array([
                z3.Int("a" + str(k) + "[" + str(i) + "]", ctx=ctx)
                for i in range(self.dim)
            ]),
            z3.Int("b" + str(k), ctx=ctx)
        ) for k in range(self.naf)]
        
        for af in afs:
            for ai in af.a:
                solver.add(ai <= +self.cmax)
                solver.add(ai >= -self.cmax)
            solver.add(af.beta <= +self.cmax)
            solver.add(af.beta >= -self.cmax)
            
        for x in self.xs_inside:
            for af in afs:
                solver.add(af.eval(x) <= 0)
            
        for x in self.xs_outside:
            cons = []
            for af in afs:
                cons.append(af.eval(x) > 0)
            solver.add(z3.Or(cons))

        for (x, y) in self.xys_transition:
            cons_x = []
            cons_y = []
            for af in afs:
                cons_x.append(af.eval(x) <= 0)
                cons_y.append(af.eval(y) <= 0)
            solver.add(z3.Implies(z3.And(cons_x), z3.And(cons_y)))

        res = solver.check()
        if res == z3.sat:
            model = solver.model()
            afs_opt = [AffForm(
                np.array([model[ai].as_long() for ai in af.a]),
                model[af.beta].as_long()
            ) for af in afs]
            return True, afs_opt
        else:
            return False, None