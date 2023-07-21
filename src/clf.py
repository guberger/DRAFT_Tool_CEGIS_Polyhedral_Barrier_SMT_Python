import numpy as np
import z3

class AffForm:
    def __init__(self, a, beta):
        self.a = a
        self.beta = beta

    def __repr__(self):
        return "<Affine form a:%s, beta:%s>" % (self.a, self.beta)

    def eval(self, x):
        return np.dot(self.a, x) + self.beta
    
################################################################################
# Generator

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

################################################################################
# Verifier

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
        
################################################################################
# Learner

class Piece:
    def __init__(self, A, b):
        self.A = A
        self.b = b
        self.afs_dom = []

class LearnerError(Exception):
    def __init__(self, *args: object):
        super().__init__(*args)

class Learner:
    def __init__(self, dim, naf, cmax, xmax):
        self.dim = dim
        self.naf = naf
        self.cmax = cmax
        self.xmax = xmax
        self.pieces = []
        self.afs_init = []
        self.afs_safe = []

    def find_invariant(self, iter_max):
        gen = Generator(self.dim, self.naf, self.cmax)
        verif_in = VerifierInclude(self.dim, self.xmax)
        verif_in.afs_inside.extend(self.afs_init)
        verif_out = VerifierInclude(self.dim, self.xmax)
        verif_out.afs_outside.extend(self.afs_safe)
        verifs_trans = []
        for piece in self.pieces:
            verif = VerifierTransition(self.dim, piece.A, piece.b, self.xmax)
            verif.afs_dom.extend(piece.afs_dom)
            verifs_trans.append(verif)
        
        iter = 0

        while True:
            iter = iter + 1
            if iter > iter_max:
                print("Max iter reached")
                return None

            print('\nIter %5d\n - Generate...' % iter, end='', flush=True)

            status, afs_inv = gen.find_candidate()
            print(' done')

            if not status:
                print("Infeasible")
                return None

            print('\n - Verify Inside...', end='', flush=True)
            verif_in.afs_outside.clear()
            verif_in.afs_outside.extend(afs_inv)
            status, x = verif_in.check()
            if status:
                print(' CE found: %s' % x)
                gen.xs_inside.append(x)
                continue
            else:
                print(' No CE found')

            print('\n - Verify Outside...', end='', flush=True)
            verif_out.afs_inside.clear()
            verif_out.afs_inside.extend(afs_inv)
            status, x = verif_out.check()
            if status:
                print(' CE found: %s' % x)
                gen.xs_outside.append(x)
                continue
            else:
                print(' No CE found')

            print('\n - Verify Transition...', end='', flush=True)
            status = False
            for verif_trans in verifs_trans:
                verif_trans.afs_inv.clear()
                verif_trans.afs_inv.extend(afs_inv)
                status, x = verif_trans.check()
                if status:
                    print(' CE found: %s' % x)
                    y = verif_trans.A @ x + verif_trans.b
                    gen.xys_transition.append((x, y))
                    break
            if status:
                continue
            else:
                print(' No CE found')
                break

        print('Valid CLF')
        return afs_inv