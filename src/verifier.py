import numpy as np
import z3
from .z3utils import get_val_int, get_val_real

class VerifierInclude:
    def __init__(self, dim, isint, xmax):
        self.dim = dim
        self.isint = isint
        if self.isint:
            assert isinstance(xmax, int)
        self.xmax = xmax
        self.afs_inside = []
        self.afs_outside = []

    def check(self):
        ctx = z3.Context()
        solver = z3.Solver(ctx=ctx)
        make_var = z3.Int if self.isint else z3.Real
        x = np.array([
            make_var("x" + "[" + str(i) + "]", ctx=ctx)
            for i in range(self.dim)
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
            get_val = get_val_int if self.isint else get_val_real
            x_opt = np.array([get_val(model, xi) for xi in x])
            return True, x_opt
        else:
            return False, None
        
class VerifierTransition:
    def __init__(self, dim, isint, xmax):
        self.dim = dim
        self.isint = isint
        if self.isint:
            assert isinstance(xmax, int)
        self.xmax = xmax
        self.pieces = []
        self.afs_inv = []

    def check(self):
        ctx = z3.Context()
        solver = z3.Solver(ctx=ctx)
        make_var = z3.Int if self.isint else z3.Real
        x = np.array([
            make_var("x" + "[" + str(i) + "]", ctx=ctx)
            for i in range(self.dim)
        ])
        y = np.array([
            make_var("y" + "[" + str(i) + "]", ctx=ctx)
            for i in range(self.dim)
        ])
        
        for xi in x:
            solver.add(xi <= +self.xmax)
            solver.add(xi >= -self.xmax)

        cons = []
        for piece in self.pieces:
            z = y - (piece.A @ x + piece.b)
            cons_pre = [zi == 0 for zi in z]
            cons_post = []
            for af in piece.afs_dom:
                cons_pre.append(af.eval(x) <= 0)
            for af in self.afs_inv:
                cons_pre.append(af.eval(x) <= 0)
                cons_post.append(af.eval(y) <= 0)
            cons.append(z3.Implies(z3.And(cons_pre), z3.And(cons_post)))
        solver.add(z3.Not(z3.And(cons)))

        res = solver.check()
        if res == z3.sat:
            model = solver.model()
            get_val = get_val_int if self.isint else get_val_real
            x_opt = np.array([get_val(model, xi) for xi in x])
            y_opt = np.array([get_val(model, yi) for yi in y])
            return True, x_opt, y_opt
        else:
            return False, None, None