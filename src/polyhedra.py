import numpy as np

class AffForm:
    def __init__(self, a, beta):
        self.a = a
        self.beta = beta

    def __repr__(self):
        return "<AF a:%s, beta:%s>" % (self.a, self.beta)

    def eval(self, x):
        return np.dot(self.a, x) + self.beta