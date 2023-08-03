from context import src
import numpy as np
import unittest
from src.generator import Generator

class TestBasicGenerator(unittest.TestCase):
    def __init__(self, methodName: str = ...):
        super().__init__(methodName)
        print("Test Generator")
    
    def test_1D_int_1(self):
        gen = Generator(1, 3, True, None, 1, 100)

        gen.xs_inside.append(np.array([1]))
        gen.xs_inside.append(np.array([3]))
        gen.xs_outside.append(np.array([5]))
        gen.xs_outside.append(np.array([-5]))

        status, afs = gen.find_candidate()

        self.assertTrue(status)
        self.assertEqual(len(afs), 3)

        gen.xys_transition.append((np.array([2]), np.array([4.5])))

        status, afs = gen.find_candidate()

        self.assertFalse(status)

        gen.amax = 2

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
    
    def test_2D_int_1(self):
        gen = Generator(2, 3, True, None, 1, 100)

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

        gen.betamax = 0

        status, afs = gen.find_candidate()

        self.assertFalse(status)

    def test_1D_real_1(self):
        gen = Generator(1, 3, False, 0.4999, None, 100)

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

        gen.eps = 0.2499

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
    
    def test_2D_real_1(self):
        gen = Generator(2, 3, False, 0.4999, None, 100)

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

        gen.eps = 0.5001

        status, afs = gen.find_candidate()

        self.assertFalse(status)

if __name__ == '__main__':
    unittest.main()