from context import src
import numpy as np
import unittest
from src.polyhedra import AffForm
from src.verifier import VerifierInclude, VerifierTransition

class TestBasicVerifier(unittest.TestCase):
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

if __name__ == '__main__':
    unittest.main()