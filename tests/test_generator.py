from context import src
import numpy as np
import unittest
from src.generator import Generator

class TestBasicGenerator(unittest.TestCase):
    def __init__(self, methodName: str = ...):
        super().__init__(methodName)
        print("Test Generator")

    def test_1D_1(self):
        gen = Generator(1, 3, 0.5, 100)

        gen.xs_inside.append(np.array([1]))
        gen.xs_inside.append(np.array([4]))
        gen.xs_outside.append(np.array([5]))
        gen.xs_outside.append(np.array([-5]))

        status, afs = gen.find_candidate()

        self.assertTrue(status)
        self.assertEqual(len(afs), 3)

        gen.xys_transition.append((np.array([2]), np.array([4.5])))

        status, afs = gen.find_candidate()

        self.assertFalse(status)

        gen.eps = 0.25

        status, afs = gen.find_candidate()

        self.assertTrue(status)
        self.assertEqual(len(afs), 3)

        gen.xys_transition.append((np.array([0]), np.array([6])))

        status, afs = gen.find_candidate()

        self.assertTrue(status)
        self.assertEqual(len(afs), 3)

        gen.xys_transition.append((np.array([1]), np.array([-1])))

        status, afs = gen.find_candidate()

        self.assertFalse(status)
    
    def test_2D_1(self):
        gen = Generator(2, 3, 0.49999, 100)

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

        gen.eps = 0.50001

        status, afs = gen.find_candidate()

        self.assertFalse(status)

if __name__ == '__main__':
    unittest.main()