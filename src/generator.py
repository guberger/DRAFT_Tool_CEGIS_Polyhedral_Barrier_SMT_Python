import numpy as np
import z3
from .polyhedra import AffForm
from .z3utils import get_val_int, get_val_real

class Generator:
    def __init__(self, dim, naf, isint, eps, amax, betamax):
        self.dim = dim
        self.naf = naf
        self.isint = isint
        if self.isint:
            assert eps is None
            assert isinstance(amax, int)
            assert isinstance(betamax, int)
            self.eps = 0
            self.amax = amax
            self.betamax = betamax
        else:
            assert amax is None
            self.eps = eps
            self.amax = 1
            self.betamax = betamax
        self.xs_inside = []
        self.xys_transition = []
        self.xs_outside = []

    def find_candidate(self):
        ctx = z3.Context()
        solver = z3.Solver(ctx=ctx)
        make_var = z3.Int if self.isint else z3.Real
        afs = [AffForm(
            np.array([
                make_var("a" + str(k) + "[" + str(i) + "]", ctx=ctx)
                for i in range(self.dim)
            ]),
            make_var("b" + str(k), ctx=ctx)
        ) for k in range(self.naf)]
        
        for af in afs:
            for ai in af.a:
                solver.add(ai <= +self.amax)
                solver.add(ai >= -self.amax)
            solver.add(af.beta <= +self.betamax)
            solver.add(af.beta >= -self.betamax)
            
        for x in self.xs_inside:
            for af in afs:
                solver.add(af.eval(x) <= -self.eps)
            
        for x in self.xs_outside:
            cons = []
            for af in afs:
                cons.append(af.eval(x) > +self.eps)
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
            get_val = get_val_int if self.isint else get_val_real
            afs_opt = [AffForm(
                np.array([get_val(model, ai) for ai in af.a]),
                get_val(model, af.beta)
            ) for af in afs]
            return True, afs_opt
        else:
            return False, None