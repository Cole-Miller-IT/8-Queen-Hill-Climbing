#Program to solve the 8-puzzle problem using heuristics and the A* algorithm
#H1 is the amount of misplaced tiles
#H2 is the Manhatten distance 
#H3 is the sum of tiles misplaced rows and columns

################ Main Program ##########################
import time
import random
import heapq
import math
import sys
import random
from collections import defaultdict, deque, Counter
from itertools import combinations

FIFOQueue = deque
LIFOQueue = list


class Problem(object):
    """The abstract class for a formal problem. A new domain subclasses this,
    overriding `actions` and `results`, and perhaps other methods.
    The default heuristic is 0 and the default action cost is 1 for all states.
    When you create an instance of a subclass, specify `initial`, and `goal` states
    (or give an `is_goal` method) and perhaps other keyword args for the subclass."""

    def __init__(self, initial=None, goal=None, **kwds):
        self.__dict__.update(initial=initial, goal=goal, **kwds)

    def actions(self, state):
        raise NotImplementedError

    def result(self, state, action):
        raise NotImplementedError

    def is_goal(self, state):
        return state == self.goal

    def action_cost(self, s, a, s1):
        return 1

    def h(self, node):
        return 0

    def __str__(self):
        return '{}({!r}, {!r})'.format(type(self).__name__, self.initial, self.goal)


class Node:
    """A Node in a search tree."""
    def __init__(self, state, parent=None, action=None, path_cost=0):
        self.path_cost = None
        self.state = None
        self.__dict__.update(state=state, parent=parent, action=action, path_cost=path_cost)

    def __repr__(self):
        return '<{}>'.format(self.state)

    def __len__(self):
        return 0 if self.parent is None else (1 + len(self.parent))

    def __lt__(self, other):
        return self.path_cost < other.path_cost


failure = Node('failure', path_cost=math.inf)  # Indicates an algorithm couldn't find a solution.
cutoff = Node('cutoff', path_cost=math.inf)  # Indicates iterative deepening search was cut off.

def expand(problem, node):
    """Expand a node, generating the children nodes."""
    s = node.state
    for action in problem.actions(s):
        s1 = problem.result(s, action)
        cost = node.path_cost + problem.action_cost(s, action, s1)
        yield Node(s1, node, action, cost)


def path_actions(node):
    """The sequence of actions to get to this node."""
    if node.parent is None:
        return []
    return path_actions(node.parent) + [node.action]


def path_states(node):
    """The sequence of states to get to this node."""
    if node in (cutoff, failure, None):
        return []
    return path_states(node.parent) + [node.state]


class PriorityQueue:
    """A queue in which the item with minimum f(item) is always popped first."""

    def __init__(self, items=(), key=lambda x: x):
        self.key = key
        self.items = []  # a heap of (score, item) pairs
        for item in items:
            self.add(item)

    def add(self, item):
        """Add item to the queuez."""
        pair = (self.key(item), item)
        heapq.heappush(self.items, pair)

    def pop(self):
        """Pop and return the item with min f(item) value."""
        return heapq.heappop(self.items)[1]

    def top(self):
        return self.items[0][1]

    def __len__(self):
        return len(self.items)




def hillClimbRandomRestart(problem):
    currentNode = Node(problem.initial)
    
    searching = True
    while(searching):
        print("The current board state is: ")
        PrintBoard(currentNode.state)
        
        #if we found a board with no queens attacking eachother (a goal state)
        if problem.is_goal(currentNode.state):
            searching = False
            return currentNode.state  
        
        #Search for the next move to take
        else:
            #print("not at goal state")
            #generate all potential next states. so each queen can move to one of the other 7 empty spaces in its column and this is done for every one of the 8 queens
            # so there are 8 * 7 = 56 possible next states to calculate     pg. 112 of the text book
        
            #Just generate one potential next state first to make sure it works



            #Determine which is the best (least amount of conflicts neighbor) to take

            #if all neighbors are worse (<=) to the current node then we have hit a local maximum
                #return currentNode #implment random restart here and decrement maxRestarts if the maxConflicts is not 0 (i.e. not at a goal state)
              
        
            #currentNode = bestNeighbor
        

            #current = neighbor
            searching = False


#The 8-Queen problem class that contains the heuristics, actions, goal state, etc..
class EightQueen(Problem):
    #Arrange 8 queens so that none of them are attacking eachother on an 8x8 chess board

    def __init__(self, initial):
        self.initial = initial

    def actions(self, state):
        return -1

    def result(self, state, action):
        return -1

    
    def checkQueenConflicts(self, state):
        return -1
    
    #Checks if the board contains any conflicts
    def is_goal(self, board):
        size = len(board)
        for i in range(size):
            for j in range(i + 1, size):
                # Check if queens are in the same row
                if board[i] == board[j]:
                    return False
                # Check for diagonal attacks
                if abs(board[i] - board[j]) == abs(i - j):
                    return False
        # If no attacks are found, then it's a goal state
        return True


    #h = number of conflicts/attacks between the queens
    def h1(self, node):
        return -1
    
    
def PrintBoard(queenPositions):
        size = len(queenPositions)  # The board size
        for row in range(size):
            line = ""
            for column in range(size):
                if queenPositions[column] == row:
                    line += "Q "
                else:
                    line += ". "
            print(line)
        print("\n")
        
############################################## Main Loop ######################################

running = True
while (running):
    #Create a random board state for 8-Queen problem. ##static for testing
    board = [1, 2, 3, 1, 5, 4, 0, 7]
    noConflictsBoard = [0, 6, 3, 5, 7, 1, 4, 2]
    
    #initalize the problem
    e1 = EightQueen(noConflictsBoard)
    print("The initial board is: ")
    PrintBoard(e1.initial)
    
    
    #perform the hill climbing algorithm on the problem
    solution = hillClimbRandomRestart(e1)
    print("The solution is: ")
    PrintBoard(solution)
    
    running = False
