# fp-chalmers

Ordered seminar reports and Agda implementations (fpclimate.agda)

## SDP simple solver in Python (sdp-simple-solver.py)

Mimicking the Agda implementations on backwards induction. An object of the SDP class is instantiated with a polymorphic type of states (X -> list or dict depending if time dependent or not) and controls (Y -> dict or nested dict), a transition function (next) and corresponding rewards. Two examples have been tested:

#### The Generation Dilemma

Three teakable parameters:

- alpha -> probability of staying in GU (1-alpha -> prob of transitioning to B)
- beta  -> probability of staying in BT (1-beta  -> prob of transitioning to GS)
- steps -> number of steps for backwards induction

```

gen_instance = GenerationDilemma(alpha = 0.5, beta = 0.5, steps = gen_steps)
gen_sdp = SDP(gen_instance.X, gen_instance.Y, gen_instance.next, gen_instance.reward)
```

#### The Cylinder Problem

Example taken from the paper "Sequential decision problems, dependently typed solutions". We ensure the viability and reachability of the time-dependent states by construction, leading therefore to better efficiency.

```
cylinder_instance = Cylinder()
cylinder_sdp = SDP(cylinder_instance.X, cylinder_instance.Y, cylinder_instance.next, cylinder_instance.reward)
```

#### Output example

```
$ python sdp-simple-solver.py 
# GENERATION DILEMMA


t          Policy t
--------------------------------------------------
0          {'GU': 'b', 'GS': None, 'BT': None, 'B': None}
1          {'GU': 'b', 'GS': None, 'BT': None, 'B': None}
2          {'GU': 'b', 'GS': None, 'BT': None, 'B': None}
3          {'GU': 'a', 'GS': None, 'BT': None, 'B': None}
4          {'GU': 'a', 'GS': None, 'BT': None, 'B': None}


# CYLINDER PROBLEM


t          Policy t
--------------------------------------------------
0          {'b': 'R', 'c': 'R', 'd': 'A', 'e': 'L'}
1          {'c': 'R', 'd': 'A', 'e': 'A'}
2          {'d': 'R', 'e': 'A'}
3          {'e': 'L'}
4          {'d': 'R', 'e': 'L'}
5          {'c': 'A', 'd': 'L', 'e': 'A'}
6          {'b': 'R', 'c': 'L', 'd': 'L', 'e': 'L'}
7          {'a': 'A', 'b': 'A', 'c': 'A', 'd': 'A', 'e': 'A'}
```
