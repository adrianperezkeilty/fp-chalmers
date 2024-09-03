from random import randint
from types import FunctionType

###########
# helpers #
########### 

# postulate argmax    : {A : Set } → (f : A → Val)    → List A → A
def argmax(A: list, f: FunctionType) -> int:
    if len(A) == 0: return None
    b = A[0]
    if len(A) == 1: return b
    for a in A:
        if f(a) > f(b): b = a
    return b

def print_output(optPolSeq):
    print('\n')
    print("t".ljust(10, " "), "Policy t")
    print('-'*50)
    for i, p in enumerate(optPolSeq):
        print(str(i).ljust(10, " "),p)
    print('\n')

##################################################################################################### 
# SDP class                                                                                         #
# - X: states                   -> list[state]                                                      #
#                                   or                                                              #
#                                   dict(key = t, value = list[state])                              #
# - Y: controls                 -> dict(key = state, value = list[state])                           #
#                                  or                                                               #
#                                  dict(key = t, value = dict(key = state, value = list[state]))    #
# - next: transition function   -> function(t, state, control) : X[t+1]                             #
# - reward                      -> dict(key = (t, x, y, next(t,x,y), value = reward_value))         #
##################################################################################################### 

class SDP:
    def __init__(self, X, Y, next, reward):
        self.X = X
        self.Y = Y
        self.next = next
        self.reward = reward

        # allow polymorhism handling between dict and list
        self.X_is_list = type(self.X) is list

    # -- value of a policy sequence through Bellman's equation where 
    # measure = sum 
    # fmap = List               
    def val(self, t, ps, x) -> int:
        if len(ps) == 0: return 0 
        p = ps[0]                           # fetch last policy
        n = self.next(t, x, p[x])           # fetch next value
        return self.reward[(t, x, p[x], n)] + self.val(t+1, ps[1:], n)

    # optExt : {t n : Nat} → PolicySeq (suc t) n → Policy t
    def optExt(self, t, ps) -> dict:
        p = {}
        if self.X_is_list: X = self.X
        else: X = self.X[t]
        for x in X:
            if self.X_is_list: Y = self.Y[x]
            else: Y = self.Y[t][x]
            p[x] = argmax(Y, lambda y : self.reward[(t, x, y, self.next(t, x, y))] + self.val(t+1, ps, self.next(t, x, y)))
        return p

    # backward induction
    # bi t (suc n) = let ps = bi (suc t) n in optExt ps :: ps
    def bi(self, t, n) -> list[dict]:
        if n == 0: return []
        ps = self.bi(t + 1, n - 1)
        return [self.optExt(t, ps)] + ps
    

#####################################################################################################################
# Generation Dilemma SDP class                                                                                      #
# alpha -> probability of staying in GU (1-alpha -> prob of transitioning to B)                                     #
# beta  -> probability of staying in BT (1-beta  -> prob of transitioning to GS)                                    #
#####################################################################################################################

class GenerationDilemma:
    
    def __init__(self, alpha, beta, steps) -> None:

        self.alpha  = alpha
        self.beta   = beta
        self.steps   = steps

        self.X = ['GU', 'GS', 'BT', 'B']
        self.Y = {
            'GU': ['a','b'],
            'GS': [],
            'BT': [],
            'B' : []
        }

        self.reward = {}
        for t in range(steps):
            self.reward[(t, 'GU', 'a', 'GU')]       = 3
            self.reward[(t, 'GU', 'a', 'B' )]       = -5
            self.reward[(t, 'GU', 'b', 'BT')]       = -1
            self.reward[(t, 'BT', None, 'GS')]      = 5
            self.reward[(t, 'BT', None, 'BT')]      = -1
            self.reward[(t, 'B',  None, 'B')]       = -5
            self.reward[(t, 'GS',  None, 'GS')]     = 5

    def next(self, t, x, y) -> str:
        match x,y:
            case 'GU', 'a'  : return {True: 'GU', False: 'B'}[randint(1,100) <= (self.alpha * 100)]  
            case 'GU', 'b'  : return 'BT'
            case 'BT', _    : return {True: 'BT', False: 'GS'}[randint(1,100) <= (self.beta * 100)]
            case 'B', _     : return 'B'
            case 'GS', _    : return 'GS'
            case _,_        : raise Exception('invalid tuple')


#####################################################################################################################
# Cylinder SDP class                                                                                                #
# SDP cilinder problem from "Sequential decision problems, dependently typed solutions"                             #
# Account for non-viable and unreachable states in state space and decision making                                  #
# By construction, if a tuple (t, x = X[t], y = Y[t][x]) is found, then it must be a viable and reachable one       #
#####################################################################################################################

class Cylinder:

    global all_states
    all_states = ['a', 'b', 'c', 'd', 'e']
    
    def __init__(self) -> None:

        self.X = {
            0: ['b', 'c', 'd', 'e'],
            1: ['c', 'd', 'e'],
            2: ['d', 'e'],
            3: ['e'],
            4: ['d', 'e'],
            5: ['c', 'd', 'e'],
            6: ['b', 'c', 'd', 'e'],
            7: all_states,
        }
        # 'A' -> ahead, 'R' -> right, 'L' -> left
        self.Y = {
            0: {
                'b': ['R'],
                'c': ['A', 'R'],
                'd': ['A', 'R', 'L'],
                'e': ['A', 'L']
            },
            1: {
                'c': ['R'],
                'd': ['A', 'R'],
                'e': ['A', 'L']
            },
            2: {
                'd': ['R'],
                'e': ['A']
            },
            3: {
                'e': ['A', 'L']
            },
            4: {
                'd': ['A', 'R', 'L'],
                'e': ['A', 'L']
            },
            5: {
                'c': ['A', 'R', 'L'],
                'd': ['A', 'R', 'L'],
                'e': ['A', 'L']
            },
            6: {
                'b': ['A', 'R', 'L'],
                'c': ['A', 'R', 'L'],
                'd': ['A', 'R', 'L'],
                'e': ['A', 'L']
            },
            7: {
                'a': ['A', 'R'],
                'b': ['A', 'R', 'L'],
                'c': ['A', 'R', 'L'],
                'd': ['A', 'R', 'L'],
                'e': ['A', 'L']
            }
        }
        # postulate reward : (t : Nat) → (x : X t) → Y t x → X (suc t) → Val
        # in this case (t,x,y) determines a unique next element (next t x y) since we are not using probabilities (M X = list(X)). 
        # we fix random rewards for each tuple (t,x,y,next(t,x,y))
        self.reward = {}
        for t in range(len(self.Y)):
            for x in self.X[t]:
                for y in self.Y[t][x]:
                    n = self.next(t, x, y)
                    self.reward[(t, x, y, n)] = randint(1,100)

    def next(self, t, x, y) -> str:
        i = all_states.index(x)
        if y == 'R': return all_states[i+1]
        if y == 'L': return all_states[i-1]
        return x
    

#########
# TESTS #
#########

# generation dilemma instance
print('# GENERATION DILEMMA')
gen_steps = 5

gen_instance = GenerationDilemma(alpha = 0.5, beta = 0.5, steps = gen_steps)
gen_sdp = SDP(gen_instance.X, gen_instance.Y, gen_instance.next, gen_instance.reward)

print_output(gen_sdp.bi(0, gen_steps))  

####################################################################################################### 
# cylinder SDP instance
print('# CYLINDER PROBLEM')

cylinder_instance = Cylinder()
cylinder_sdp = SDP(cylinder_instance.X, cylinder_instance.Y, cylinder_instance.next, cylinder_instance.reward)

print_output(cylinder_sdp.bi(0, 8))