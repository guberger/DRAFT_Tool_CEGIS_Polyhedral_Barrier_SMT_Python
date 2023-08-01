import numpy as np
import z3

class VerifierInclude:
    def __init__(self, dim, xmax):
        self.dim = dim
        self.xmax = xmax
        self.afs_inside = []
        self.afs_outside = []

    def check(self):
        ctx = z3.Context()
        solver = z3.Solver(ctx=ctx)
        x = np.array([
            z3.Int("x" + "[" + str(i) + "]", ctx=ctx) for i in range(self.dim)
        ])
        
        for xi in x:
            solver.add(xi <= +self.xmax)
            solver.add(xi >= -self.xmax)

        cons_inside = []
        for af in self.afs_inside:
            cons_inside.append(af.eval(x) <= 0)
        cons_outside = []
        for af in self.afs_outside:
            cons_outside.append(af.eval(x) > 0)
        solver.add(z3.And(z3.And(cons_inside), z3.Or(cons_outside)))

        res = solver.check()
        if res == z3.sat:
            model = solver.model()
            x_opt = np.array([model[xi].as_long() for xi in x])
            return True, x_opt
        else:
            return False, None
        
class VerifierTransition:
    def __init__(self, dim, A, b, xmax):
        self.dim = dim
        self.A = A
        self.b = b
        self.xmax = xmax
        self.afs_dom = []
        self.afs_inv = []

    def check(self):
        ctx = z3.Context()
        solver = z3.Solver(ctx=ctx)
        x = np.array([
            z3.Int("x" + "[" + str(i) + "]", ctx=ctx) for i in range(self.dim)
        ])
        y = self.A @ x + self.b
        
        for xi in x:
            solver.add(xi <= +self.xmax)
            solver.add(xi >= -self.xmax)

        cons_x = []
        cons_y = []
        for af in self.afs_dom:
            cons_x.append(af.eval(x) <= 0)
        for af in self.afs_inv:
            cons_x.append(af.eval(x) <= 0)
            cons_y.append(af.eval(y) > 0)
        solver.add(z3.And(z3.And(cons_x), z3.Or(cons_y)))

        res = solver.check()
        if res == z3.sat:
            model = solver.model()
            x_opt = np.array([model[xi].as_long() for xi in x])
            return True, x_opt
        else:
            return False, None