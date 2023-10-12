from lib.massfun import Massfun, Event, f_CEU, f_JEU, f_TBEU
from lib.util import IndexedVector as Profile
import numpy as np
import pickle
import time


class SProfile(Profile):
    """Profile of profiles"""

    def flatten(self):
        p = {}
        for i, pi in self:
            for ti, ai in pi:
                p[(i,ti)] = ai
        return Profile(p)

    def when(self, t):
        return Profile({i: self[i][t[i]] for i in self.keys()})

    @staticmethod
    def of_profile(p):
        sp = {}
        for (i,ti) in p.keys():
            if not i in sp.keys():
                sp[i] = []
            sp[i].append(ti)
        for i, tis in sp.items():
            sp[i] = Profile({ti: p[(i,ti)] for ti in tis})
        return SProfile(sp)

    @staticmethod
    def iter_all(players, actions, types):
        flat_players = []
        for i in players:
            for ti in types[i]:
                flat_players.append((i,ti))
        flat_actions = {(i,ti): actions[i] for i,ti in flat_players}
        for fp in Profile.iter_all(flat_players, flat_actions):
            yield SProfile.of_profile(fp)



class AbstractGame(object):
    def __init__(self, players, n_actions, name="Game"):
        self.players = players
        self.n_actions = n_actions
        self.name = name

        self.rev_players = {v:k for k, v in enumerate(players)}

    @property
    def n_players(self):
        return len(self.players)
    
    @property
    def size(self):
        raise NotImplementedError("AbstractGame.size")

    def playsin(self, i):
        return i in self.players


class AbstractCGame(AbstractGame):
    def __init__(self, players, n_actions, name="CGame"):
        AbstractGame.__init__(self, players, n_actions, name)

    def utility(self, i, a):
        raise NotImplementedError("AbstractCGame.utility")

    def utility_mat(self):
        raise NotImplementedError("AbstractCGame.utmat")

    def mkprofile(self, profile, rev_indexes):
        return [profile[rev_indexes[i]] for i in self.players]




class CGame(AbstractCGame):

    def __init__(self, players, n_actions, umat, name="CGame"):
        AbstractCGame.__init__(self, players, n_actions, name) 
        self.umat = umat

    def utility(self, i, a):
        return self.umat[tuple([self.rev_players[i]]+a)]

    def utility_mat(self):
        return self.umat

    @staticmethod
    def random(players, n_actions, name="RandomGame"):
        shape = tuple([len(players)]+[n_actions[i] for i in players])
        umat = np.random.rand(*shape)
        return CGame(players, n_actions, umat, name)

    @property
    def size(self):
        ret = 1
        for i in self.umat.shape:
            ret *= i
        return ret


class HGGame(AbstractCGame):

    def __init__(self, players, n_actions, games, name="HGGame"):
        AbstractCGame.__init__(self, players, n_actions, name) 
        self.games = games
        
    def utility(self, i, a):
        ret = 0
        for g in self.games:
            if g.playsin(i):
##                print("+", g.utility(i, g.mkprofile(a, self.rev_players)))
                ret += g.utility(i, g.mkprofile(a, self.rev_players))
        return ret
##        return sum([g.utility(i, g.mkprofile(a, self.rev_players))
##                    for g in self.games
##                    if g.playsin(i)])

    @property
    def size(self):
        return sum([g.size for g in self.games])

    
class BelGame(AbstractGame):

    def __init__(self, players, n_actions, types, games, bpa, name="BelGame"):
        AbstractCGame.__init__(self, players, n_actions, name) 
        self.types = types
        self.games = games
        self.bpa = bpa

    @property
    def n_players(self):
        return len(self.players)

    def utility(self, t, i, a):
        return self.games[t].utility(i,a)

    def sutility(self, t, i, s):
        p = s.when(t)
        return self.utility(t, i, [p[i] for i in self.players])

    def xeu(self, i, ti, sp, cond, f_xeu):
        cond_evt = Event([t for t in self.bpa.fod
                          if t[i] == ti])
        m = self.bpa.conditional(cond, cond_evt)
        ret = 0
        for x, mx in m.iter_focals():
            v = f_xeu([self.sutility(t, i, sp) for t in x])
##            print("xeu:", v, "x", mx)
            ret += v * mx
##        print(ret)
            
##        print( sum([mx * f_xeu([self.sutility(t, i, sp) for t in x])
##                    for x, mx in m.iter_focals()]))
        return ret
    
    @property
    def size(self):
        return sum([g.size for g in self.games.values()])

    
    @staticmethod
    def random(players, n_actions, types, n_focals=10, k_add=2, name="RandomBelGame"):
        games = {}
        fod = []
        for theta in Profile.iter_all(players, types):
            fod.append(theta)
            games[theta] = CGame.random(players, n_actions, name="Game if theta=%s"%theta)
        bpa = Massfun.random(fod, n_focals, k=k_add)
        return BelGame(players, n_actions, types, games, bpa, name)

    def _hr_players(self):
        cplayers = []
        for i in self.players:
            for ti in self.types[i]:
                cplayers.append((i,ti))
        return cplayers

    def direct_transform(self, f_xeu):
        cplayers = self._hr_players()
        games = []
        for x, mx in self.bpa.iter_focals():
            local_players = set()
            for t in x:
                for i, ti in t.items():
                    local_players.add((i,ti))
            local_players = list(local_players)
            shape = [len(local_players)]+[self.n_actions[i] for i,ti in local_players]
            utility = np.zeros(shape=shape)
            _rev_players = {k: i for i,k in enumerate(local_players)}
            for i, ti in local_players:
                cond_evt = Event([t for t in self.bpa.fod if t[i]==ti])
                mtix = mx / self.bpa.psup(cond_evt)
                for p in Profile.iter_all(local_players,
                                          {(i,ti):range(self.n_actions[i]) for i,ti in local_players}):
                    keys = tuple([_rev_players[(i,ti)]] + [p[i] for i in local_players])
                    us = []
                    for t in x:
                        if t in cond_evt:
                            a = [p[(i,t[i])] for i in self.players]
                            us.append(self.utility(t,i,a))
                    utility[keys] = f_xeu(us) * mtix
            games.append(CGame(local_players, self.n_actions, utility, name="From focal %s"%x))
        return HGGame(cplayers, self.n_actions, games, name="Direct transform")

    def conditioned_transform(self, cond, f_xeu):
        cplayers = self._hr_players()
        games = []
        focals = set()
        bpas = {}
        for (i,ti) in cplayers:
            cond_evt = Event([t for t in self.bpa.fod if t[i]==ti])
            bpas[(i,ti)] = self.bpa.conditional(cond, cond_evt)
            for x, _ in bpas[(i,ti)].iter_focals():
                focals.add(x)
        for x in focals:
            local_players = set()
            for t in x:
                for i, ti in t.items():
                    local_players.add((i,ti))
            local_players = list(local_players)
            shape = [len(local_players)]+[self.n_actions[i] for i,ti in local_players]
            utility = np.zeros(shape=shape)
            _rev_players = {k: i for i,k in enumerate(local_players)}
            for i, ti in local_players:
                mtix = bpas[(i,ti)].mass(x)
                for p in Profile.iter_all(local_players, {(i,ti):range(self.n_actions[i]) for i,ti in local_players}):
                    keys = tuple([_rev_players[(i,ti)]] + [p[i] for i in local_players])
                    us = []
                    for t in x:
                        a = [p[(i,t[i])] for i in self.players]
                        us.append(self.utility(t,i,a))
                    utility[keys] = f_xeu(us) * mtix
            games.append(CGame(local_players, self.n_actions, utility, name="From focal %s"%x))
        return HGGame(cplayers, self.n_actions, games, name="Conditioned transform")
            
    def tbm_transform(self):
        cplayers = self._hr_players()
        games = []
        for t in self.bpa.fod:
            local_players = set()
            for i, ti in t.items():
                local_players.add((i,ti))
            local_players = list(local_players)
            shape = [len(local_players)]+[self.n_actions[i] for i,ti in local_players]
            utility = np.zeros(shape=shape)
            _rev_players = {k: i for i,k in enumerate(local_players)}
            for i, ti in local_players:
                if t[i] == ti:
                    cond_evt = Event([t for t in self.bpa.fod if t[i]==ti])
                    betp = 0
                    for x, mx in self.bpa.iter_focals():
                        if x.intersects(cond_evt) and t in x:
                            betp += mx / len(Event.intersection(x,cond_evt))
                    betp /= self.bpa.psup(cond_evt)
                    for p in Profile.iter_all(local_players, {(i,ti):range(self.n_actions[i]) for i,ti in local_players}):
                        keys = tuple([_rev_players[(i,ti)]] + [p[i] for i in local_players])
                        a = [p[(i,t[i])] for i in self.players]
                        utility[keys] = self.utility(t,i,a) * betp
            games.append(CGame(local_players, self.n_actions, utility, name="From theta %s"%x))
        return HGGame(cplayers, self.n_actions, games, name="TBM transform")

        
    def is_proper(self, cond):
        if cond == "dempster":
            f = self.bpa.psup
        else:
            raise NotImplementedError("BelGame.is_proper('dempster')")
        
        for i in self.players:
            for ti in self.types[i]:
                cond_evt = Event([t for t in self.bpa.fod if t[i]==ti])
                if f(cond_evt) == 0:
                    return False
        return True
    

    def isHReq(self, cgame, cond, f_xeu):
        # Check players
        i_ti = []
        if set(cgame.players) != set(self._hr_players()):
            print("HReq: invalid players")
            print(set(cgame.players), "!=", set(i_ti))
            return False

        # Check actions:
        if self.n_actions != cgame.n_actions:
            return False

        # Check utility
        for p in Profile.iter_all(cgame.players,
                                  {(i,ti):range(self.n_actions[i]) for i,ti in cgame.players}):
            a = [p[i] for i in cgame.players]
            sp = SProfile.of_profile(p)
            for (i,ti) in cgame.players:
                u = cgame.utility((i,ti), a)
                xeu = self.xeu(i, ti, sp, cond, f_xeu)
                if abs(u - xeu) > 0.0000001:
                    print("HReq:", u, "!=", xeu, "<<<<<False>>>>>")
                    return False
        return True


# CSV separator
SEP = ","

# Print CSV function
def print_csv(*args, **kwargs):
    print(*args, sep=SEP, flush=True, **kwargs)


def run_test(f_name, f_XEU, cond, n_focals, k_add, n_players, n_actions, n_types, check=True):

    print_csv(n_focals, k_add, cond, f_name, n_players,
              ";".join(["%d"%n_actions[i] for i in range(n_players)]),
              ";".join(["%d"%n_types[i] for i in range(n_players)]), end=SEP)

    # Player list and type dict
    players = range(n_players)
    types = {i : range(n_types[i]) for i in players}

    # Instanciate belg
    t = time.time()
    belg = BelGame.random(players, n_actions, types, n_focals=n_focals, k_add=k_add)
    t = time.time() - t
    print_csv(len(belg.bpa.fod), len([1 for _ in belg.bpa.iter_focals()]),
              belg.size, "%.6f"%t, belg.is_proper(cond), end=SEP)

    # Save BelG (for re-run if needed)
    with open("/home/ppomco/Documents/These/workspace/GSG/tmp.pkl", "wb") as f:
        pickle.dump(belg, f)

    # Load BelG (for re-run if needed)
    #with open("/home/ppomco/Documents/These/workspace/GSG/tmp.pkl", "rb") as f:
    #    belg = pickle.load(f)


    # Direct transform: only for dempster conditioning
    if cond == "dempster":
        t = time.time()
        hg = belg.direct_transform(f_XEU)
        t = time.time() - t

        # Check utility equality
        b = None
        if check:
            b = belg.isHReq(hg, "dempster", f_XEU)

        # Max number of players of local games
        lg = max([g.n_players for g in hg.games])

        print_csv(b, hg.size, "%.6f"%t, lg, end=SEP)
    else:
        print_csv(None, None, None, None, end=SEP)


    # Conditioned transform: for any conditioning and XEU
    t = time.time()
    hg = belg.conditioned_transform("dempster", f_XEU)
    t = time.time() - t

    # Check utility equality
    b = None
    if check:
        b = belg.isHReq(hg, "dempster", f_XEU)

    # Max number of players of local games
    lg = max([g.n_players for g in hg.games])

    print_csv(b, hg.size, "%.6f"%t, lg, end=SEP)


    # TBM transform: only for TBEU and dempster
    if cond == "dempster" and f_name == "TBEU":
        t = time.time()
        hg = belg.tbm_transform()
        t = time.time() - t

        # Check utility equality
        b = None
        if check:
            b = belg.isHReq(hg, "dempster", f_XEU)

        # Max number of players of local games
        lg = max([g.n_players for g in hg.games])

        print_csv(b, hg.size, "%.6f"%t, lg, end=SEP)
    else:
        print_csv(None, None, None, None, end=SEP)


    # End of line
    print_csv()



        
if __name__ == "__main__":

    # Check utility equality
    check = False

    # XEU functions
    f_XEUs = {
##        "CEU": f_CEU,
##        "JEU(0.8)": f_JEU(0.8),
        "TBEU": f_TBEU
        }

    # Conditionals
    conditionals = [
        'dempster'
        ]

    
    # Parameter ranges
    n_focals_range = range(5,11)
    k_add_range = range(2,11)
    n_players_range = range(2,4)
    n_actions_range = range(2,4)
    n_types_range = range(2,4)

    # Number of tests for any parameter combination
    n_tests = 1



    print_csv("n_focals", "k_add", "cond", "xeu", "n_p", "n_a", "n_t", "n_fod", "n_focals2", "belg_size", "belg_time", "proper_belg", "dt_ok", "dt_size", "dt_time", "dt_max_lg", "ct_ok", "ct_size", "ct_time", "ct_max_lg", "tt_ok", "tt_size", "tt_time", "tt_max_lg")
    
    for f_name, f_XEU in f_XEUs.items():
        for cond in conditionals:
            for n_focals in n_focals_range:
                for k_add in k_add_range:
                    for n_players in n_players_range:
                        for n_actions in Profile.iter_all(range(n_players), {i: n_actions_range for i in range(n_players)}):
                            for n_types in Profile.iter_all(range(n_players), {i: n_types_range for i in range(n_players)}):
                           #for n_types in n_types_range:
                                for _ in range(n_tests):
                                    run_test(f_name, f_XEU, cond, n_focals, k_add, n_players,
                                             n_actions, n_types, check=check)
