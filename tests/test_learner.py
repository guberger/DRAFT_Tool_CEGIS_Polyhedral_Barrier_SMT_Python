from context import src
import numpy as np
import unittest
from src.polyhedra import AffForm
from src.system import Piece
from src.learner import Learner
 
class TestBasicLearner(unittest.TestCase):
    def __init__(self, methodName: str = ...):
        super().__init__(methodName)
        print("Test Learner")

    def test_2D_2(self):
        # 2D, 3 affine functions
        lear = Learner(2, 1, 0.5, 100, 100)

        # rot +90 deg, trans (+1, 0)
        A = np.array([[0, 0.5], [0.5, 0]])
        b = np.array([0, 0])
        lear.pieces.append(Piece(A, b))

        # init Rect[(0, 0), (1, 1)]
        lear.afs_init.append(AffForm(np.array([-1, 0]), 1))
        lear.afs_init.append(AffForm(np.array([+1, 0]), 1))
        # safe Rect[(-2, -2)] & (x1 + x2 >= -2)
        lear.afs_safe.append(AffForm(np.array([-1, 0]), -2))
        lear.afs_safe.append(AffForm(np.array([+1, 0]), -2))
        lear.afs_safe.append(AffForm(np.array([0, -1]), -2))
        lear.afs_safe.append(AffForm(np.array([0, +1]), -2))

        afs = lear.find_invariant(1000)

        self.assertIsNotNone(afs)
        print(afs)

        # init Point (0.5, 0.5)
        lear.afs_init.clear()
        lear.afs_init.append(AffForm(np.array([-1, 0]), 0.5))
        lear.afs_init.append(AffForm(np.array([0, -1]), 0.5))
        lear.afs_init.append(AffForm(np.array([+1, +1]), -1))

        afs = lear.find_invariant(1000)

        self.assertIsNone(afs)

        # More facets
        lear.naf = 3

        afs = lear.find_invariant(1000)

        self.assertIsNotNone(afs)
        print(afs)

        # scaling 10x, unrestricted domain
        A = np.array([[10, 0], [0, 10]])
        b = np.array([0, 0])
        lear.pieces.append(Piece(A, b))

        afs = lear.find_invariant(1000)

        self.assertIsNone(afs)

        # restricted domain
        lear.pieces[1].afs_dom.append(AffForm(np.array([+1, +1]), 2))

        afs = lear.find_invariant(1000)

        self.assertIsNotNone(afs)
        print(afs)
        

if __name__ == '__main__':
    unittest.main()