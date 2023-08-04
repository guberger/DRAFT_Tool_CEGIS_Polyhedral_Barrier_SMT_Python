from context import src
import numpy as np
import unittest
from src.polyhedra import AffForm, Polyhedron, Region
from src.system import Piece
from src.learner import Learner
 
class TestBasicLearner(unittest.TestCase):
    def __init__(self, methodName: str = ...):
        super().__init__(methodName)
        print("Test Learner")

    def test_2D_int_1(self):
        # rot +90 deg, trans (+1, 0)
        A1 = np.array([[0, -1], [+1, 0]])
        b1 = np.array([+1, 0])
        piece1 = Piece(A1, b1, Region([
            Polyhedron([]),
        ]))
        # scaling 10x, restricted domain
        A2 = np.array([[10, 0], [0, 10]])
        b2 = np.array([0, 0])
        piece2 = Piece(A2, b2, Region([
            Polyhedron([
                AffForm(np.array([+1, +1]), 0),
            ]),
        ]))

        # init empty
        rinit = Region([
            Polyhedron([
                AffForm(np.array([-1, 0]), 1),
                AffForm(np.array([+1, 0]), 1),
            ]),
        ])
        # safe Rect[(-2, -2)] & (x1 + x2 >= -2)
        runsafe = Region([
            Polyhedron([AffForm(np.array([-1, 0]), +2)]),
            Polyhedron([AffForm(np.array([+1, 0]), +2)]),
            Polyhedron([AffForm(np.array([0, -1]), +2)]),
            Polyhedron([AffForm(np.array([0, +1]), +2)]),
            Polyhedron([AffForm(np.array([+1, +1]), +2)]),
        ])

        # 2D, 3 affine functions
        lear = Learner(2, 1, True, None, 3, 100, True, 100,
                       [piece1, piece2], rinit, runsafe)

        pinv = lear.find_invariant(1000)

        self.assertIsNotNone(pinv)
        print(pinv)

        # init Rect[(0, 0), (1, 1)]
        lear.rinit = Region([
            Polyhedron([
                AffForm(np.array([-1, 0]), 0),
                AffForm(np.array([+1, 0]), -1),
                AffForm(np.array([0, -1]), -0),
                AffForm(np.array([0, +1]), -1),
            ]),
        ])

        pinv = lear.find_invariant(1000)

        self.assertIsNone(pinv)

        lear.naf = 3

        pinv = lear.find_invariant(1000)

        self.assertIsNotNone(pinv)
        print(pinv)

    def test_2D_real_1(self):
        # rot +90 deg, scaling 0.5x
        A1 = np.array([[0, 0.5], [0.5, 0]])
        b1 = np.array([0, 0])
        piece1 = Piece(A1, b1, Region([
            Polyhedron([]),
        ]))

        # init Empty
        rinit = Region([
            Polyhedron([
                AffForm(np.array([-1, 0]), 1),
                AffForm(np.array([+1, 0]), 1),
            ]),
        ])
        # safe Rect[(-2, -2)] & (x1 + x2 >= -2)
        runsafe = Region([
            Polyhedron([AffForm(np.array([-1, 0]), +2)]),
            Polyhedron([AffForm(np.array([+1, 0]), +2)]),
            Polyhedron([AffForm(np.array([0, -1]), +2)]),
            Polyhedron([AffForm(np.array([0, +1]), +2)]),
            Polyhedron([AffForm(np.array([+1, +1]), +2)]),
        ])

        # 2D, 3 affine functions
        lear = Learner(2, 1, False, 0.5, None, 100, False, 100,
                       [piece1], rinit, runsafe)

        pinv = lear.find_invariant(1000)

        self.assertIsNotNone(pinv)
        print(pinv)

        # init Point (0.5, 0.5)
        lear.rinit = Region([
            Polyhedron([
                AffForm(np.array([-1, 0]), 0.5),
                AffForm(np.array([0, -1]), 0.5),
                AffForm(np.array([+1, +1]), -1),
            ]),
        ])

        pinv = lear.find_invariant(1000)

        self.assertIsNone(pinv)

        # More facets
        lear.naf = 3

        pinv = lear.find_invariant(1000)

        self.assertIsNotNone(pinv)
        print(pinv)

        # scaling 10x, unrestricted domain
        A2 = np.array([[10, 0], [0, 10]])
        b2 = np.array([0, 0])
        piece2 = Piece(A2, b2, Region([
            Polyhedron([]),
        ]))
        lear.pieces.append(piece2)

        pinv = lear.find_invariant(1000)

        self.assertIsNone(pinv)

        # restricted domain
        lear.pieces[1].rdom.ps[0].pinv.append(AffForm(np.array([+1, +1]), 2))

        pinv = lear.find_invariant(1000)

        self.assertIsNotNone(pinv)
        print(pinv)
        
if __name__ == '__main__':
    unittest.main()