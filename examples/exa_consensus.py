from context import src
import numpy as np
from scipy import spatial, optimize
from matplotlib import pyplot as plt
from mpl_toolkits.mplot3d.art3d import Poly3DCollection
from src.polyhedra import AffForm, Polyhedron, Region
from src.system import Piece
from src.learner import Learner

# vars: (x, y, t)

vmax = 5
vmin = -5
T = vmax - vmin

A0 = np.array([[1, 0, 0], [0, 1, 0], [0, 0, 0]])
A1 = np.array([[1, 0, 0], [0, 1, 0], [0, 0, 1]])
xgy = [AffForm(np.array([-1, +1, 0]), 1)]
ygx = [AffForm(np.array([+1, -1, 0]), 1)]
xey = [
    AffForm(np.array([+1, -1, 0]), 0),
    AffForm(np.array([-1, +1, 0]), 0),
]
tlT = [
    AffForm(np.array([0, 0, -1]), 0),
    AffForm(np.array([0, 0, +1]), -(T - 1)),
]
teT = [
    AffForm(np.array([0, 0, -1]), +T),
    AffForm(np.array([0, 0, +1]), -T),
]
pieces = []

# x > y, t < T
b = np.array([-1, 0, 1])
piece = Piece(A1, b, Region([Polyhedron(xgy + tlT)]))
pieces.append(piece)

# y > x, t < T
b = np.array([0, -1, 1])
piece = Piece(A1, b, Region([Polyhedron(ygx + tlT)]))
pieces.append(piece)

# x = y, t < T
b = np.array([0, 0, 1])
piece = Piece(A1, b, Region([Polyhedron(xey + tlT)]))
pieces.append(piece)

# x > y, t = T
b = np.array([-1, 0, 0])
piece = Piece(A1, b, Region([Polyhedron(xgy + teT)]))
pieces.append(piece)

# y > x, t = T
b = np.array([0, -1, 0])
piece = Piece(A1, b, Region([Polyhedron(ygx + teT)]))
pieces.append(piece)

# x = y, t = T
b = np.array([0, 0, 0])
piece = Piece(A1, b, Region([Polyhedron(xey + teT)]))
pieces.append(piece)

tmax = 2*T
dv = vmax - vmin
fig = plt.figure()
ax = plt.axes(xlim=(-1, tmax + 2), ylim=(vmin - 0.01*dv, vmax + 0.01*dv))
x = np.array([vmax - 1, vmin + 1, 0])

for t in range(tmax):
    s = '.' if x[2] == T else 'x'
    ax.plot(t, x[0], ls=None, marker=s, ms=10, c='red')
    ax.plot(t, x[1], ls=None, marker=s, ms=10, c='blue')
    flag = False
    for piece in pieces:
        if piece.rdom.eval(x) <= 0:
            flag = True
            x = piece.A @ x + piece.b
            break
    assert flag

# init
rinit = Region([
    Polyhedron([
        AffForm(np.array([-1, 0, 0]), +vmin),
        AffForm(np.array([+1, 0, 0]), -vmax),
        AffForm(np.array([0, -1, 0]), +vmin),
        AffForm(np.array([0, +1, 0]), -vmax),
        AffForm(np.array([0, 0, -1]), +0),
        AffForm(np.array([0, 0, +1]), -0),
    ])
])
# safe
runsafe = Region([
    Polyhedron([AffForm(np.array([+1, 0, 0]), -vmin)]),
    Polyhedron([AffForm(np.array([-1, 0, 0]), +vmax)]),
    Polyhedron([AffForm(np.array([0, +1, 0]), -vmin)]),
    Polyhedron([AffForm(np.array([0, -1, 0]), +vmax)]),
    Polyhedron([AffForm(np.array([0, 0, +1]), 0)]),
    Polyhedron([AffForm(np.array([0, 0, -1]), T)]),
    Polyhedron([
        AffForm(np.array([0, 0, -1]), T - 1),
        AffForm(np.array([+1, -1, 0]), 0),
    ]),
    Polyhedron([
        AffForm(np.array([0, 0, -1]), T - 1),
        AffForm(np.array([-1, +1, 0]), 0),
    ])
])

xmax = 2*max(abs(vmin), abs(vmax), abs(T)) + 2
lear = Learner(3, 7, True, None, 3, 200, True, xmax,
               pieces, rinit, runsafe)

pinv = lear.find_invariant(1000)
print(pinv)

fig = plt.figure()
ax = plt.axes(projection='3d',
              xlim=(vmin - 1, vmax + 1),
              ylim=(vmin - 1, vmax + 1),
              zlim=(-1, T + 1))

q = 0
afs = [af for af in pinv.afs if np.linalg.norm(af.a) > 0.1]
A = np.array([list(af.a) + [1.0] for af in afs])
b = np.array([-af.beta for af in afs])
c = np.array([0, 0, 0, -1])
res = optimize.linprog(c, A_ub=A, b_ub=b, bounds=(None, None))
assert res['success'] and res['status'] == 0 and res['fun'] < 0
A[:, -1] = -b
hs = spatial.HalfspaceIntersection(A, res['x'][0:3])
points = list(hs.intersections)
ch = spatial.ConvexHull(points)
verts_list = [[ch.points[i, :] for i in simplex] for simplex in ch.simplices]
polylist = Poly3DCollection(verts_list, facecolor='red', alpha=0.7,
                            ec='black', lw=1)
ax.add_collection3d(polylist)

plt.show()