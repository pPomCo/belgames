"""
Mass functions
"""
import itertools as it
import numpy as np

from lib.util import IndexedVector as vector
from lib.util import DefaultDict as ddict




class Event(set):
    
    @staticmethod
    def iter_all(fod):
        """Iterator over all events. fod: list"""
        fod = list(fod)
        for p in vector.iter_all(fod, {k:[True,False] for k in fod}):
            yield Event([x for x,b in p.items() if b])

    @staticmethod
    def intersection(x,y):
        return Event(set.intersection(x,y))

    def intersects(self, other):
        return set.intersection(self,other) != set()

    def __str__(self):
        return "{" + ",".join(sorted([str(x) for x in self])) + "}"

    def __hash__(self):
        return hash(str(self))

    def __eq__(self, other):
        return str(self) == str(other)





class AbstractMassfun(object):

    def iter_focals(self):
        raise NotImplementedError("AbstractMassfun.iter_focals")

    def mass(self,event):
        raise NotImplementedError("AbstractMassfun.mass")


    def pinf(self, event):
        v = 0
        for x, mx in self.iter_focals():
            if x.issubset(event):
                v += mx
        return v
        
    def psup(self, event):
        v = 0
        for x, mx in self.iter_focals():
            if x.intersects(event):
                v += mx
        return v

    @property
    def fod(self):
        fod = set()
        for x, _ in self.iter_focals():
            fod = set.union(fod,x)
        return Event(fod)

    @property
    def k_degree(self):
        return max([len(x) for x,_ in self.iter_focals()])

    @property
    def n_focals(self):
        return len(list(self.iter_focals()))

    @property
    def info(self):
        return "\n\t- ".join([
            "Massfun info:",
            "FOD: %s"%self.fod,
            "k-add degree: %d"%self.k_degree,
            "n focals: %d"%self.n_focals])
    

    def dempster_precondition(self, event):
        return self.psup(event) != 0

    def dempster_conditional(self, event):
        m = ddict(default=0)
        norm = 0
        for x, mx in self.iter_focals():
            mxe = Event.intersection(event, x)
            if len(mxe) > 0:
                m[mxe] += mx
                norm += mx
        return Massfun({x:mx/norm for x,mx in m.items()})

    def conditional(self, cond, event):
        if cond == "dempster":
            return self.dempster_conditional(event)
        else:
            raise NotImplementedError("Massfun.conditional('%s', _)"%cond)
        

    def xeu(self, u, f_xeu):
        ret = 0
        for x, mx in self.iter_focals():
            ret += mx * f_xeu([u(w) for w in x])
        return ret


class Massfun(AbstractMassfun):
    """Massfun from dict: key=x, value=m(x)"""
    def __init__(self, m):
        self._m = ddict(m, default=0)

    def mass(self, x):
        return self._m[x]

    def iter_focals(self):
        for x, mx in self._m.items():
            yield x, mx


    @staticmethod
    def random(fod, n_focals, k=None):
        """Random mass function
            - fod: list,
            - n_focals: int
            - k: int/None = k-additivity degree
            """
        m = ddict(default=0)
        norm = 0
        if k is None:
            k = len(fod)
        for _ in range(n_focals):
            x = Event(np.random.choice(fod, k))
            mx = np.random.rand(1)[0]*1000//10
            norm += mx
            m[x] += mx
        return(Massfun({x:mx/norm for x,mx in m.items()}))
        
        

class AbstractConditioning(object):

    @staticmethod
    def precond(bpa, c):
        raise NotImplementedError("Conditioning.precond")

    @staticmethod
    def cond(bpa, c):
        raise NotImplementedError("Conditioning.cond")


class DempsterCond(AbstractConditioning):
    
    def precond(bpa, c):
        return bpa.psup(c) != 0
    
    def cond(bpa, c):
        ret = []
        norm = 0
        for x, mx in bpa.iter_focals():
            if x.intersects(c):
                ret.append((Event.intersection(x,c), mx))
                norm += mx
        return ListBpa([(x, mx/norm) for x,mx in ret])




f_CEU = min
def f_JEU(alpha):
    return lambda x: alpha * min(x) + (1-alpha) * max(x)
f_TBEU = lambda x: sum(x) / len(x)
