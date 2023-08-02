from .generator import Generator
from .verifier import VerifierInclude, VerifierTransition

class LearnerError(Exception):
    def __init__(self, *args: object):
        super().__init__(*args)

class Learner:
    def __init__(self, dim, naf, eps, betamax, xmax):
        self.dim = dim
        self.naf = naf
        self.eps = eps
        self.betamax = betamax
        self.xmax = xmax
        self.pieces = []
        self.afs_init = []
        self.afs_safe = []

    def find_invariant(self, iter_max):
        gen = Generator(self.dim, self.naf, self.eps, self.betamax)
        verif_in = VerifierInclude(self.dim, self.xmax)
        verif_in.afs_inside.extend(self.afs_init)
        verif_out = VerifierInclude(self.dim, self.xmax)
        verif_out.afs_outside.extend(self.afs_safe)
        verif_trans = VerifierTransition(self.dim, self.xmax)
        verif_trans.pieces.extend(self.pieces)
        
        iter = 0

        while True:
            iter = iter + 1
            if iter > iter_max:
                print("Max iter reached")
                return None

            print('Iter %d\n - Generate...' % iter, end='', flush=True)

            status, afs_inv = gen.find_candidate()
            print(' done')

            if not status:
                print("Infeasible")
                return None

            print(' - Verify Inside...', end='', flush=True)
            verif_in.afs_outside.clear()
            verif_in.afs_outside.extend(afs_inv)
            status, x = verif_in.check()
            if status:
                print(' CE found: %s' % x)
                gen.xs_inside.append(x)
                continue
            else:
                print(' No CE found')

            print(' - Verify Outside...', end='', flush=True)
            verif_out.afs_inside.clear()
            verif_out.afs_inside.extend(afs_inv)
            status, x = verif_out.check()
            if status:
                print(' CE found: %s' % x)
                gen.xs_outside.append(x)
                continue
            else:
                print(' No CE found')

            print(' - Verify Transition...', end='', flush=True)
            verif_trans.afs_inv.clear()
            verif_trans.afs_inv.extend(afs_inv)
            status, x, y = verif_trans.check()
            if status:
                print(' CE found: %s -> %s' % (x, y))
                gen.xys_transition.append((x, y))
                continue
            else:
                print(' No CE found')
                break

        print('Valid CLF')
        return afs_inv