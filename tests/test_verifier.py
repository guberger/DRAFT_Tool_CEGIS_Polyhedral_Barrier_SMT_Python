from math import sqrt
from context import src
import numpy as np
import unittest
from src.polyhedra import AffForm
from src.system import Piece
from src.verifier import VerifierInclude, VerifierTransition

class TestBasicVerifier(unittest.TestCase):
    def __init__(self, methodName: str = ...):
        super().__init__(methodName)
        print("Test Verifier")

    def test_include_2D_int_1(self):
        verif = VerifierInclude(2, True, 100)

        verif.afs_inside.append(AffForm(np.array([-1, -1]), -4))
        verif.afs_inside.append(AffForm(np.array([-1, +1]), -4))
        verif.afs_inside.append(AffForm(np.array([+1, -1]), -4))
        verif.afs_inside.append(AffForm(np.array([+1, +1]), -4))

        verif.afs_outside.append(AffForm(np.array([-1, 0]), -4))
        verif.afs_outside.append(AffForm(np.array([+1, 0]), -4))
        verif.afs_outside.append(AffForm(np.array([0, -1]), -4))
        verif.afs_outside.append(AffForm(np.array([0, +1]), -4))

        status, x = verif.check()

        self.assertFalse(status)

        verif.afs_outside.append(AffForm(np.array([-1, 0]), -3))

        status, x = verif.check()

        self.assertTrue(status)
        self.assertEqual(len(x), 2)

    def test_transistion_2D_int_1(self):
        verif = VerifierTransition(2, True, 100)

        A1 = np.array([[0, -1], [+1, 0]])
        b1 = np.array([+1,  -1])
        piece = Piece(A1, b1)
        piece.afs_dom.append(AffForm(np.array([-1, 0]), 0))
        verif.pieces.append(piece)

        A2 = np.array([[+1, 0], [0, -1]])
        b2 = np.array([0, 0])
        piece = Piece(A2, b2)
        verif.pieces.append(piece)

        verif.afs_inv.append(AffForm(np.array([-1, -1]), -2))
        verif.afs_inv.append(AffForm(np.array([-1, +1]), -2))
        verif.afs_inv.append(AffForm(np.array([+1, -1]), -2))
        verif.afs_inv.append(AffForm(np.array([+1, +1]), -2))

        status, x, y = verif.check()

        self.assertTrue(status)
        self.assertEqual(len(x), 2)
        self.assertEqual(len(y), 2)
        self.assertAlmostEqual(np.linalg.norm(y - (A1 @ x + b1)), 0)

        verif.pieces[0].afs_dom.append(AffForm(np.array([0, -1]), 0))

        status, x, y = verif.check()

        self.assertFalse(status)

    def test_include_2D_real_1(self):
        verif = VerifierInclude(2, False, 100)

        verif.afs_inside.append(AffForm(np.array([-1, -1]), -2.5))
        verif.afs_inside.append(AffForm(np.array([-1, +1]), -2.5))
        verif.afs_inside.append(AffForm(np.array([+1, -1]), -2.5))
        verif.afs_inside.append(AffForm(np.array([+1, +1]), -2.5))

        verif.afs_outside.append(AffForm(np.array([-1, 0]), -2.5))
        verif.afs_outside.append(AffForm(np.array([+1, 0]), -2.5))
        verif.afs_outside.append(AffForm(np.array([0, -1]), -2.5))
        verif.afs_outside.append(AffForm(np.array([0, +1]), -2.5))

        status, x = verif.check()

        self.assertFalse(status)

        verif.afs_outside.append(AffForm(np.array([-1, 0]), -1.25))

        status, x = verif.check()

        self.assertTrue(status)
        self.assertEqual(len(x), 2)

    def test_transistion_2D_real_1(self):
        verif = VerifierTransition(2, False, 100)

        A1 = np.array([[sqrt(1/2), -sqrt(1/2)], [+sqrt(1/2), sqrt(1/2)]])
        b1 = np.array([0,  0.99999 - sqrt(2)])
        piece = Piece(A1, b1)
        piece.afs_dom.append(AffForm(np.array([-1, 0]), 0))
        verif.pieces.append(piece)

        A2 = np.array([[0.5, 0], [0, 0.5]])
        b2 = np.array([0.5, 0])
        piece = Piece(A2, b2)
        verif.pieces.append(piece)

        verif.afs_inv.append(AffForm(np.array([-1, -1]), -1))
        verif.afs_inv.append(AffForm(np.array([-1, +1]), -1))
        verif.afs_inv.append(AffForm(np.array([+1, -1]), -1))
        verif.afs_inv.append(AffForm(np.array([+1, +1]), -1))

        status, x, y = verif.check()

        self.assertTrue(status)
        self.assertEqual(len(x), 2)
        self.assertEqual(len(y), 2)
        self.assertAlmostEqual(np.linalg.norm(y - (A1 @ x + b1)), 0)

        verif.pieces[0].afs_dom.append(AffForm(np.array([0, -1]), 0))

        status, x, y = verif.check()

        self.assertFalse(status)

if __name__ == '__main__':
    unittest.main()