from math import cos, pi, sin
from context import src
import numpy as np
from matplotlib import pyplot as plt
from src.polyhedra import AffForm, Polyhedron, Region
from src.system import Piece
from src.learner import Learner

def rot_mat(theta):
    return np.array([[cos(theta), -sin(theta)], [+sin(theta), cos(theta)]])

alpha = 0.5
theta = pi/5
A = alpha*rot_mat(theta)
b = np.array([0, 0])
piece = Piece(A, b, Region([Polyhedron([])]))

# init Rect halfside rho
rho = 0.25
rinit = Region([
    Polyhedron([
        AffForm(np.array([-1, 0]), -rho),
        AffForm(np.array([+1, 0]), -rho),
        AffForm(np.array([0, -1]), -rho),
        AffForm(np.array([0, +1]), -rho),
    ]),
])
# safe Rect halfside 4
runsafe = Region([
    Polyhedron([AffForm(np.array([-1, 0]), +2)]),
    Polyhedron([AffForm(np.array([+1, 0]), +2)]),
    Polyhedron([AffForm(np.array([0, -1]), +2)]),
    Polyhedron([AffForm(np.array([0, +1]), +2)]),
])

lear = Learner(2, 5, False, 0.15, None, 100, False, 10,
               [piece], rinit, runsafe)

pinv = lear.find_invariant(1000)

print(pinv)

fig = plt.figure()
ax = plt.axes(xlim=(-2.1, 2.1), ylim=(-2.1, 2.1))

dx = 0.01
rs = np.arange(-2.1, 2.1, dx)
X1, X2 = np.meshgrid(rs, rs, indexing='ij')
Z = np.zeros((len(rs), len(rs)))
W = np.zeros((len(rs), len(rs)))
for i, x1 in enumerate(rs):
    for j, x2 in enumerate(rs):
        x = np.array([x1, x2])
        y = A @ x
        z_opt = -float('inf')
        w_opt = -float('inf')
        for af in pinv.afs:
            z = af.eval(x)
            z_opt = max(z_opt, z)
            w = af.eval(y)
            w_opt = max(w_opt, w)
        Z[i, j] = z_opt
        W[i, j] = w_opt

ax.contour(X1, X2, Z, levels=(0.0,), colors='blue')
ax.contour(X1, X2, W, levels=(0.0,), colors='red')

plt.show()