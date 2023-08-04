from .polyhedra import AffForm, Polyhedron, Region
from .generator import Generator
from .verifier import VerifierInclude, VerifierTransition

class LearnerError(Exception):
    def __init__(self, *args: object):
        super().__init__(*args)

class Learner:
    def __init__(self, dim, naf, isintg, eps, amax, betamax, isintv, xmax,
                 pieces, rinit, runsafe):
        self.dim = dim
        self.naf = naf
        self.isintg = isintg
        self.eps = eps
        self.amax = amax
        self.betamax = betamax
        self.isintv = isintv
        self.xmax = xmax
        self.pieces = pieces
        self.rinit = rinit
        self.runsafe = runsafe

    def find_invariant(self, iter_max):
        gen = Generator(self.dim, self.naf, self.isintg,
                        self.eps, self.amax, self.betamax)
        verif_in = VerifierInclude(self.dim, self.isintv, self.xmax,
                                   self.rinit, Region([]))
        verif_out = VerifierInclude(self.dim, self.isintv, self.xmax,
                                    Region(Polyhedron([])), self.runsafe)
        verif_trans = VerifierTransition(self.dim, self.isintv, self.xmax,
                                         self.pieces, Region(Polyhedron([])))
        
        iter = 0

        while True:
            iter = iter + 1
            if iter > iter_max:
                print("Max iter reached")
                return None

            print('Iter %d\n - Generate...' % iter, end='', flush=True)

            status, pinv = gen.find_candidate()
            print(' done')

            if not status:
                print("Infeasible")
                return None

            print(' - Verify Inside...', end='', flush=True)
            verif_in.rout = Region([
                Polyhedron([AffForm(-af.a, -af.beta)])
                for af in pinv.afs
            ])
            status, x = verif_in.check()
            if status:
                print(' CE found: %s' % x)
                gen.xs_inside.append(x)
                continue
            else:
                print(' No CE found')

            print(' - Verify Outside...', end='', flush=True)
            verif_out.rin = Region([pinv])
            status, x = verif_out.check()
            if status:
                print(' CE found: %s' % x)
                gen.xs_outside.append(x)
                continue
            else:
                print(' No CE found')

            print(' - Verify Transition...', end='', flush=True)
            verif_trans.rinv = Region([pinv])
            status, x, y = verif_trans.check()
            if status:
                print(' CE found: %s -> %s' % (x, y))
                gen.xys_transition.append((x, y))
                continue
            else:
                print(' No CE found')
                break

        print('Valid CLF')
        return pinv