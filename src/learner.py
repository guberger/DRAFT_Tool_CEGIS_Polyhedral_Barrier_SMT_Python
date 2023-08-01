from .generator import Generator
from .verifier import VerifierInclude, VerifierTransition

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