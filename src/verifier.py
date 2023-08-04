import numpy as np
import z3
from .z3utils import get_val_int, get_val_real

class VerifierInclude:
    def __init__(self, dim, isint, xmax, rin, rout):
        self.dim = dim
        self.isint = isint
        if self.isint:
            assert isinstance(xmax, int)
        self.xmax = xmax
        self.rin = rin
        self.rout = rout

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

        cons_A = []
        for p in self.rin.ps:
            cons_ = []
            for af in p.afs:
                cons_.append(af.eval(x) <= 0)
            cons_A.append(z3.And(cons_, ctx))
        con_A = z3.Or(cons_A, ctx)
        cons_B = []
        for p in self.rout.ps:
            cons_ = []
            for af in p.afs:
                cons_.append(af.eval(x) < 0)
            cons_B.append(z3.And(cons_, ctx))
        con_B = z3.Or(cons_B, ctx)
        solver.add(z3.And(con_A, con_B))

        res = solver.check()
        if res == z3.sat:
            model = solver.model()
            get_val = get_val_int if self.isint else get_val_real
            x_opt = np.array([get_val(model, xi) for xi in x])
            return True, x_opt
        else:
            return False, None
        
class VerifierTransition:
    def __init__(self, dim, isint, xmax, pieces, rinv):
        self.dim = dim
        self.isint = isint
        if self.isint:
            assert isinstance(xmax, int)
        self.xmax = xmax
        self.pieces = pieces
        self.rinv = rinv

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

        all_cons = []
        for piece in self.pieces:
            z = y - (piece.A @ x + piece.b)
            con_trans = z3.And([zi == 0 for zi in z])
            cons_dom = []
            for p in piece.rdom.ps:
                cons_ = []
                for af in p.afs:
                    cons_.append(af.eval(x) <= 0)
                cons_dom.append(z3.And(cons_, ctx))
            con_dom = z3.Or(cons_dom, ctx)
            cons_inv_x = []
            cons_inv_y = []
            for p in self.rinv.ps:
                cons_x_ = []
                cons_y_ = []
                for af in p.afs:
                    cons_x_.append(af.eval(x) <= 0)
                    cons_y_.append(af.eval(y) <= 0)
                cons_inv_x.append(z3.And(cons_x_, ctx))
                cons_inv_y.append(z3.And(cons_y_, ctx))
            con_inv_x = z3.Or(cons_inv_x, ctx)
            con_inv_y = z3.Or(cons_inv_y, ctx)
            con_A = z3.And(con_trans, con_dom, con_inv_x)
            con_B = con_inv_y
            all_cons.append(z3.Implies(con_A, con_B))
        solver.add(z3.Not(z3.And(all_cons, ctx)))

        res = solver.check()
        if res == z3.sat:
            model = solver.model()
            get_val = get_val_int if self.isint else get_val_real
            x_opt = np.array([get_val(model, xi) for xi in x])
            y_opt = np.array([get_val(model, yi) for yi in y])
            return True, x_opt, y_opt
        else:
            return False, None, None