"""
Util
"""
import itertools as it


class IndexedVector(dict):
    """Hashable dictionnary as indexed vectors

        For any key k and value v, str(k) and str(v) shouldn't
        contain neither ' ' nor ':' characters"""


    def __str__(self):
        return "[" + ' '.join(["%s:%s"%(str(k),str(v))
                               for k,v in sorted(self.items())])+"]"

    def __hash__(self):
        return hash(str(self))

    @staticmethod
    def iter_all(keys, values):
        """Cross product of the values
            - keys: list
            - values: dict (domain (list) for each key)"""
        i = {k: 0 for k in keys}
        p = {k: values[k][i[k]] for k in keys}
        yield IndexedVector(p)
        ptr = 0
        n = len(keys)
        while ptr < n:
            try:
                i[keys[ptr]] += 1
                while i[keys[ptr]] >= len(values[keys[ptr]]):
                    i[keys[ptr]] = 0
                    ptr += 1
                    i[keys[ptr]] += 1
                ptr = 0
                p = {k: values[k][i[k]] for k in keys}
            except IndexError:
                return None
            yield IndexedVector(p)


    def projection(self, keys):
        """Restriction over the given dimensions"""
        return IndexedVector({k:v for k,v in self.items() if k in keys})



class DefaultDict(dict):
    """Dictionnary with default value"""

    def __init__(self, *args, default=None):
        dict.__init__(self, *args)
        self.default = default

    def __getitem__(self, k):
        try:
            return dict.__getitem__(self, k)
        except KeyError:
            return self.default
