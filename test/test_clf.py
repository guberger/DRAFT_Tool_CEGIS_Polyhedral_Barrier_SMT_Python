import unittest
import numpy as np
from src.clf import \
    AffForm, Generator, VerifierInclude, VerifierTransition, \
    Piece, Learner

################################################################################

class TestGenerator(unittest.TestCase):
    def __init__(self, methodName: str = ...):
        super().__init__(methodName)
        print("Test Generator")

    def test_1D_1(self):
        gen = Generator(1, 5, 5)

        gen.xs_inside.append(np.array([1]))
        gen.xs_inside.append(np.array([3]))
        gen.xs_outside.append(np.array([5]))
        gen.xs_outside.append(np.array([-5]))
        gen.xys_transition.append((np.array([2]), np.array([4])))

        status, afs = gen.find_candidate()

        self.assertTrue(status)
        self.assertEqual(len(afs), 5)

        gen.xys_transition.append((np.array([4]), np.array([-5])))

        status, afs = gen.find_candidate()

        self.assertFalse(status)

    def test_1D_2(self):
        gen = Generator(1, 2, 5)

        gen.xs_inside.append(np.array([1]))
        gen.xs_inside.append(np.array([3]))
        gen.xs_outside.append(np.array([5]))
        gen.xs_outside.append(np.array([-5]))
        gen.xys_transition.append((np.array([4]), np.array([6])))

        status, afs = gen.find_candidate()                    

        self.assertTrue(status)             
        self.assertEqual(len(afs), 2)

        gen.xys_transition.append((np.array([2]), np.array([4])))

        status, afs = gen.find_candidate()

        self.assertFalse(status)
    
    def test_2D_1(self):
        gen = Generator(2, 3, 100)

        gen.xs_inside.append(np.array([-1, 0]))
        gen.xs_inside.append(np.array([+1, 0]))
        gen.xs_inside.append(np.array([0, -1]))
        gen.xs_inside.append(np.array([0, +1]))
        gen.xs_outside.append(np.array([-1, -1]))
        gen.xys_transition.append((np.array([-1, +1]), np.array([-3, -3])))
        gen.xys_transition.append((np.array([+1, -1]), np.array([-3, -3])))
        gen.xys_transition.append((np.array([+1, +1]), np.array([-3, -3])))

        status, afs = gen.find_candidate()

        self.assertFalse(status)

        gen.naf = 4

        status, afs = gen.find_candidate()

        self.assertTrue(status)
        self.assertEqual(len(afs), 4)    

################################################################################

class TestVerifier(unittest.TestCase):
    def __init__(self, methodName: str = ...):
        super().__init__(methodName)
        print("Test Verifier")

    def test_inside_2D_1(self):
        verif = VerifierInclude(2, 100)

        verif.afs_inside.append(AffForm(np.array([-1, -1]), -5))
        verif.afs_inside.append(AffForm(np.array([-1, +1]), -5))
        verif.afs_inside.append(AffForm(np.array([+1, -1]), -5))
        verif.afs_inside.append(AffForm(np.array([+1, +1]), -5))

        verif.afs_outside.append(AffForm(np.array([-1, 0]), -5))
        verif.afs_outside.append(AffForm(np.array([+1, 0]), -5))
        verif.afs_outside.append(AffForm(np.array([0, -1]), -5))
        verif.afs_outside.append(AffForm(np.array([0, +1]), -5))

        status, x = verif.check()

        self.assertFalse(status)

        verif.afs_outside.append(AffForm(np.array([-1, 0]), -3))

        status, x = verif.check()

        self.assertTrue(status)
        self.assertEqual(len(x), 2)

    def test_outside_2D_1(self):
        verif = VerifierInclude(2, 100)

        verif.afs_outside.append(AffForm(np.array([-1, 0]), -5))
        verif.afs_outside.append(AffForm(np.array([+1, 0]), -5))
        verif.afs_outside.append(AffForm(np.array([0, -1]), -5))
        verif.afs_outside.append(AffForm(np.array([0, +1]), -5))

        verif.afs_inside.append(AffForm(np.array([-1, -1]), -5))
        verif.afs_inside.append(AffForm(np.array([-1, +1]), -5))
        verif.afs_inside.append(AffForm(np.array([+1, -1]), -5))
        verif.afs_inside.append(AffForm(np.array([+1, +1]), -5))

        status, x = verif.check()

        self.assertFalse(status)

        verif.afs_outside.append(AffForm(np.array([-1, 0]), -3))

        status, x = verif.check()

        self.assertTrue(status)
        self.assertEqual(len(x), 2)

    def test_transistion_2D_1(self):
        A = np.array([[0, -1], [+1, 0]])
        b = np.array([2, -2])

        verif = VerifierTransition(2, A, b, 100)

        verif.afs_dom.append(AffForm(np.array([-1, 0]), 0))

        verif.afs_inv.append(AffForm(np.array([-1, -1]), -4))
        verif.afs_inv.append(AffForm(np.array([-1, +1]), -4))
        verif.afs_inv.append(AffForm(np.array([+1, -1]), -4))
        verif.afs_inv.append(AffForm(np.array([+1, +1]), -4))

        status, x = verif.check()

        self.assertTrue(status)
        self.assertEqual(len(x), 2)

        verif.afs_dom.append(AffForm(np.array([0, -1]), 0))

        status, x = verif.check()

        self.assertFalse(status)

################################################################################
 
class TestLearner2D(unittest.TestCase):
    def __init__(self, methodName: str = ...):
        super().__init__(methodName)
        print("Test Learner")

    def test_2D_1(self):
        # 2D, 3 affine functions
        lear = Learner(2, 3, 100, 100)
        # rot +90 deg, trans (+2, -2)
        A = np.array([[0, -1], [+1, 0]])
        b = np.array([2, -2])
        lear.pieces.append(Piece(A, b))
        # scaling 10x
        A = np.array([[10, 0], [0, 10]])
        b = np.array([0, 0])
        lear.pieces.append(Piece(A, b))
        # init Rect[(0, 0), (1, 1)]
        lear.afs_init.append(AffForm(np.array([-1, 0]), 0))
        lear.afs_init.append(AffForm(np.array([+1, 0]), -1))
        lear.afs_init.append(AffForm(np.array([0, -1]), -0))
        lear.afs_init.append(AffForm(np.array([0, +1]), -1))
        # safe Rect[(-2, -2)] & (x1 + x2 >= -2)
        lear.afs_safe.append(AffForm(np.array([-1, 0]), -2))
        lear.afs_safe.append(AffForm(np.array([+1, 0]), -2))
        lear.afs_safe.append(AffForm(np.array([0, -1]), -2))
        lear.afs_safe.append(AffForm(np.array([0, +1]), -2))
        lear.afs_safe.append(AffForm(np.array([-1, -1]), -2))

        afs = lear.find_invariant(1000)

        self.assertIsNone(afs)

    def test_2D_2(self):
        # 2D, 3 affine functions
        lear = Learner(2, 3, 3, 100)
        # rot +90 deg, trans (+1, 0)
        A = np.array([[0, -1], [+1, 0]])
        b = np.array([1, 0])
        lear.pieces.append(Piece(A, b))
        # scaling 10x, restricted domain
        A = np.array([[10, 0], [0, 10]])
        b = np.array([0, 0])
        lear.pieces.append(Piece(A, b))
        lear.pieces[1].afs_dom.append(AffForm(np.array([+1, +1]), 0))
        # init Rect[(0, 0), (1, 1)]
        lear.afs_init.append(AffForm(np.array([-1, 0]), 0))
        lear.afs_init.append(AffForm(np.array([+1, 0]), -1))
        lear.afs_init.append(AffForm(np.array([0, -1]), -0))
        lear.afs_init.append(AffForm(np.array([0, +1]), -1))
        # safe Rect[(-2, -2)] & (x1 + x2 >= -2)
        lear.afs_safe.append(AffForm(np.array([-1, 0]), -2))
        lear.afs_safe.append(AffForm(np.array([+1, 0]), -2))
        lear.afs_safe.append(AffForm(np.array([0, -1]), -2))
        lear.afs_safe.append(AffForm(np.array([0, +1]), -2))
        lear.afs_safe.append(AffForm(np.array([-1, -1]), -2))

        afs = lear.find_invariant(1000)

        self.assertIsNotNone(afs)