from math import sqrt
from context import src
import numpy as np
import unittest
from src.polyhedra import AffForm, Polyhedron, Region
from src.system import Piece
from src.verifier import VerifierInclude, VerifierTransition

class TestBasicVerifier(unittest.TestCase):
    def __init__(self, methodName: str = ...):
        super().__init__(methodName)
        print("Test Verifier")

    def test_include_2D_int_1(self):
        rin = Region([
            Polyhedron([
                AffForm(np.array([-1, -1]), -4),
                AffForm(np.array([-1, +1]), -4),
                AffForm(np.array([+1, -1]), -4),
                AffForm(np.array([+1, +1]), -4),
            ]),
        ])
        rout = Region([
            Polyhedron([AffForm(np.array([-1, 0]), +4)]),
            Polyhedron([AffForm(np.array([+1, 0]), +4)]),
            Polyhedron([AffForm(np.array([0, -1]), +4)]),
            Polyhedron([AffForm(np.array([0, +1]), +4)]),
        ])
        verif = VerifierInclude(2, True, 100, rin, rout)

        status, x = verif.check()

        self.assertFalse(status)

        verif.rin.ps.append(
            Polyhedron([
                AffForm(np.array([-1, 0]), +6),
                AffForm(np.array([+1, 0]), -6),
                AffForm(np.array([0, -1]), 0),
                AffForm(np.array([0, +1]), 0),
            ])
        )

        status, x = verif.check()

        self.assertTrue(status)
        self.assertAlmostEqual(np.linalg.norm(x - np.array([6, 0])), 0)

        verif.rout.ps[0].afs.append(
            AffForm(np.array([+1, 0]), -5)
        )

        status, x = verif.check()

        self.assertFalse(status)

    def test_transistion_2D_int_1(self):
        A1 = np.array([[0, -1], [+1, 0]])
        b1 = np.array([+2,  -2])
        piece1 = Piece(A1, b1, Region([
            Polyhedron([
                AffForm(np.array([-1, 0]), 0),
                AffForm(np.array([0, -1]), 0),
            ]),
        ]))
        A2 = np.array([[0, +1], [+1, 0]])
        b2 = np.array([0, 0])
        piece2 = Piece(A2, b2, Region([
            Polyhedron([]),
        ]))

        rinv = Region([
            Polyhedron([
                AffForm(np.array([-1, 0]), 0),
                AffForm(np.array([+1, 0]), -2),
                AffForm(np.array([0, -1]), 0),
                AffForm(np.array([0, +1]), -2),
            ]),
            Polyhedron([
                AffForm(np.array([-1, 0]), -2),
                AffForm(np.array([+1, 0]), 0),
                AffForm(np.array([0, -1]), 0),
                AffForm(np.array([0, +1]), -2),
            ]),
            Polyhedron([
                AffForm(np.array([-1, 0]), 0),
                AffForm(np.array([+1, 0]), -2),
                AffForm(np.array([0, -1]), -2),
                AffForm(np.array([0, +1]), 0),
            ]),
        ])

        verif = VerifierTransition(2, True, 100, [piece1, piece2], rinv)

        status, x, y = verif.check()

        self.assertFalse(status)

        verif.pieces[0].rdom.ps.append(
            Polyhedron([
                AffForm(np.array([-1, 0]), 0),
                AffForm(np.array([0, +1]), 0),
            ])
        )

        status, x, y = verif.check()

        self.assertTrue(status)
        self.assertEqual(len(x), 2)
        self.assertEqual(len(y), 2)
        self.assertAlmostEqual(np.linalg.norm(y - (A1 @ x + b1)), 0)

    def test_include_2D_real_1(self):
        rin = Region([
            Polyhedron([                
                AffForm(np.array([-1, -1]), 0),
                AffForm(np.array([-1, +1]), -2.5),
                AffForm(np.array([+1, -1]), -2.5),
                AffForm(np.array([+1, +1]), -2.5),
            ]),
            Polyhedron([                
                AffForm(np.array([-1, -1]), -2.5),
                AffForm(np.array([-1, +1]), -2.5),
                AffForm(np.array([+1, -1]), -2.5),
                AffForm(np.array([+1, +1]), 0),
            ]),
        ])

        rout = Region([
            Polyhedron([AffForm(np.array([-1, 0]), +2.5)]),
            Polyhedron([AffForm(np.array([+1, 0]), +2.5)]),
            Polyhedron([AffForm(np.array([0, -1]), +2.5)]),
            Polyhedron([AffForm(np.array([0, +1]), +2.5)]),
        ])

        verif = VerifierInclude(2, False, 100, rin, rout)

        status, x = verif.check()

        self.assertFalse(status)

        verif.rout.ps.append(
            Polyhedron([
                AffForm(np.array([-1, 0]), -1.25),
            ])
        )

        status, x = verif.check()

        self.assertTrue(status)
        self.assertEqual(len(x), 2)

    def test_transistion_2D_real_1(self):
        A1 = np.array([[sqrt(1/2), -sqrt(1/2)], [+sqrt(1/2), sqrt(1/2)]])
        b1 = np.array([0,  0.99999 - sqrt(2)])
        piece1 = Piece(A1, b1, Region([
            Polyhedron([
                AffForm(np.array([-1, 0]), 0),
                AffForm(np.array([0, -1]), 0),
            ]),
        ]))

        A2 = np.array([[0.5, 0], [0, 0.5]])
        b2 = np.array([0.5, 0])
        piece2 = Piece(A2, b2, Region([
            Polyhedron([]),
        ]))

        rinv = Region([
            Polyhedron([
                AffForm(np.array([-1, -1]), 0),
                AffForm(np.array([-1, +1]), -1),
                AffForm(np.array([+1, -1]), -1),
                AffForm(np.array([+1, +1]), -1),
            ]),
            Polyhedron([
                AffForm(np.array([-1, -1]), -1),
                AffForm(np.array([-1, +1]), -1),
                AffForm(np.array([+1, -1]), -1),
                AffForm(np.array([+1, +1]), 0),
            ]),
        ])

        verif = VerifierTransition(2, False, 100, [piece1, piece2], rinv)

        status, x, y = verif.check()

        self.assertFalse(status)

        verif.pieces[0].rdom.ps.append(
            Polyhedron([
                AffForm(np.array([+1, 0]), 0),
                AffForm(np.array([0, +1]), 0),
            ])
        )

        status, x, y = verif.check()

        self.assertTrue(status)
        self.assertEqual(len(x), 2)
        self.assertEqual(len(y), 2)
        self.assertAlmostEqual(np.linalg.norm(y - (A1 @ x + b1)), 0)

if __name__ == '__main__':
    unittest.main()