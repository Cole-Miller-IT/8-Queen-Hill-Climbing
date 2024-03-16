#Program to solve the 8-puzzle problem using heuristics and the A* algorithm
#H1 is the amount of misplaced tiles
#H2 is the Manhatten distance 
#H3 is the sum of tiles misplaced rows and columns

################ Main Program ##########################
import time
import tracemalloc
from memory_profiler import profile
import random
import heapq
import math
import sys
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


def best_first_search(problem, f):
    """Search nodes with minimum f(node) value first."""
    node = Node(problem.initial)

    print("Initial Heuristic: ")
    if problem.heuristic == "h1":
        print(problem.h1(node))   
    elif problem.heuristic == "h2":
        print(problem.h2(node)) 
    elif problem.heuristic == "h3":
        print(problem.h3(node)) 
    print("")

    frontier = PriorityQueue([node], key=f)
    reached = {problem.initial: node}
    while frontier:
        node = frontier.pop()
        if problem.is_goal(node.state):
            return node
        for child in expand(problem, node):
            s = child.state
            if s not in reached or child.path_cost < reached[s].path_cost:
                reached[s] = child
                frontier.add(child)
    return failure


def is_cycle(node, k=30):
    """Does this node form a cycle of length k or less?"""

    def find_cycle(ancestor, k):
        return (ancestor is not None and k > 0 and
                (ancestor.state == node.state or find_cycle(ancestor.parent, k - 1)))

    return find_cycle(node.parent, k)


def g(n):
    return n.path_cost


def astar_search(problem, h=None):
    """Search nodes with minimum f(n) = g(n) + h(n)."""
    h = h or problem.h
    return best_first_search(problem, f=lambda n: g(n) + h(n))


#8-Puzzle problem class that contains the heuristics, actions, goal state, etc..
class EightPuzzle(Problem):
    """ The problem of sliding tiles numbered from 1 to 8 on a 3x3 board,
    where one of the squares is a blank, trying to reach a goal configuration.
    A board state is represented as a tuple of length 9, where the element at index i
    represents the tile number at index i, or 0 if for the empty square, e.g. the goal:
        1 2 3
        4 5 6 ==> (1, 2, 3, 4, 5, 6, 7, 8, 0)
        7 8 _
    """

    def __init__(self, initial, goal=(1, 2, 3, 4, 5, 6, 7, 8, 0)):
    #def __init__(self, initial, goal=(0, 1, 2, 3, 4, 5, 6, 7, 8)):
        assert inversions(initial) % 2 == inversions(goal) % 2  # Parity check
        self.initial, self.goal = initial, goal
        self.heuristic = "h1"

    def actions(self, state):
        """The indexes of the squares that the blank can move to."""
        moves = ((1, 3), (0, 2, 4), (1, 5),
                 (0, 4, 6), (1, 3, 5, 7), (2, 4, 8),
                 (3, 7), (4, 6, 8), (7, 5))
        blank = state.index(0)
        return moves[blank]

    def result(self, state, action):
        """Swap the blank with the square numbered `action`."""
        s = list(state)
        blank = state.index(0)
        s[action], s[blank] = s[blank], s[action]
        return tuple(s)

    def h1(self, node):
        """The misplaced tiles heuristic."""
        return hamming_distance(node.state, self.goal)

    def h2(self, node):
        """The Manhattan heuristic."""
        X = (0, 1, 2, 0, 1, 2, 0, 1, 2)
        Y = (0, 0, 0, 1, 1, 1, 2, 2, 2)
        return sum(abs(X[s] - X[g]) + abs(Y[s] - Y[g])
                   for (s, g) in zip(node.state, self.goal) if s != 0)
    
    #Number of tiles not in there correct columns + rows
    def h3(self, node):
        #print("Goal state")
        #print(self.goal)
        #print("Next iteration")
        #print(node.state)
        #print(node.__repr__())

        heuristicValue = 0

        #for each tile (including 0)
        counter = 0 #Used to check if the current tile is in the right spot
        for tile in node.state:
            #Top row
            #Check tile 1 (top left most tile)
            if counter == 0:
                #Check row
                if ((tile != self.goal[0]) and (tile != self.goal[1]) and (tile != self.goal[2])):
                    heuristicValue = heuristicValue + 1
                    #print("Tile out of place row " + str(tile))

                #Check column
                if ((tile != self.goal[0]) and (tile != self.goal[3]) and (tile != self.goal[6])):
                    heuristicValue = heuristicValue + 1
                    #print("Tile out of place column " + str(tile))
            
            if counter == 1:
                #Check row
                if ((tile != self.goal[0]) and (tile != self.goal[1]) and (tile != self.goal[2])):
                    heuristicValue = heuristicValue + 1
                    #print("Tile out of place row " + str(tile))

                #Check column
                if ((tile != self.goal[1]) and (tile != self.goal[4]) and (tile != self.goal[7])):
                    heuristicValue = heuristicValue + 1
                    #print("Tile out of place column " + str(tile))

            if counter == 2:
                #Check row
                if ((tile != self.goal[0]) and (tile != self.goal[1]) and (tile != self.goal[2])):
                    heuristicValue = heuristicValue + 1
                    #print("Tile out of place row " + str(tile))

                #Check column
                if ((tile != self.goal[2]) and (tile != self.goal[5]) and (tile != self.goal[8])):
                    heuristicValue = heuristicValue + 1
                    #print("Tile out of place column " + str(tile))

            #################################################################################################
            #Second Row

            if counter == 3:
                #Check row
                if ((tile != self.goal[3]) and (tile != self.goal[4]) and (tile != self.goal[5])):
                    heuristicValue = heuristicValue + 1
                    #print("Tile out of place row " + str(tile))

                #Check column
                if ((tile != self.goal[0]) and (tile != self.goal[3]) and (tile != self.goal[6])):
                    heuristicValue = heuristicValue + 1
                    #print("Tile out of place column " + str(tile))
            
            if counter == 4:
                #Check row
                if ((tile != self.goal[3]) and (tile != self.goal[4]) and (tile != self.goal[5])):
                    heuristicValue = heuristicValue + 1
                    #print("Tile out of place row " + str(tile))

                #Check column
                if ((tile != self.goal[1]) and (tile != self.goal[4]) and (tile != self.goal[7])):
                    heuristicValue = heuristicValue + 1
                    #print("Tile out of place column " + str(tile))

            if counter == 5:
                #Check row
                if ((tile != self.goal[3]) and (tile != self.goal[4]) and (tile != self.goal[5])):
                    heuristicValue = heuristicValue + 1
                    #print("Tile out of place row " + str(tile))

                #Check column
                if ((tile != self.goal[2]) and (tile != self.goal[5]) and (tile != self.goal[8])):
                    heuristicValue = heuristicValue + 1
                    #print("Tile out of place column " + str(tile))
                    
            #################################################################################################
            #Third row

            if counter == 6:
                #Check row
                if ((tile != self.goal[6]) and (tile != self.goal[7]) and (tile != self.goal[8])):
                    heuristicValue = heuristicValue + 1
                    #print("Tile out of place row " + str(tile))

                #Check column
                if ((tile != self.goal[0]) and (tile != self.goal[3]) and (tile != self.goal[6])):
                    heuristicValue = heuristicValue + 1
                    #print("Tile out of place column " + str(tile))
            
            if counter == 7:
                #Check row
                if ((tile != self.goal[6]) and (tile != self.goal[7]) and (tile != self.goal[8])):
                    heuristicValue = heuristicValue + 1
                    #print("Tile out of place row " + str(tile))

                #Check column
                if ((tile != self.goal[1]) and (tile != self.goal[4]) and (tile != self.goal[7])):
                    heuristicValue = heuristicValue + 1
                    #print("Tile out of place column " + str(tile))

            if counter == 8:
                #Check row
                if ((tile != self.goal[6]) and (tile != self.goal[7]) and (tile != self.goal[8])):
                    heuristicValue = heuristicValue + 1
                    #print("Tile out of place row " + str(tile))

                #Check column
                if ((tile != self.goal[2]) and (tile != self.goal[5]) and (tile != self.goal[8])):
                    heuristicValue = heuristicValue + 1
                    #print("Tile out of place column " + str(tile))
            
            counter = counter + 1
               
        #print("Heuristic value: ")
        #print(heuristicValue)
        return heuristicValue

    #Change which heuristic the search algorithm should use
    def setHeuristic(self, heuristic):
        self.heuristic = heuristic

    #Calls one of the 8-puzzles h# methods to calculate the value of h(n)
    def h(self, node): 
        if self.heuristic == "h1":
            return self.h1(node)
        elif self.heuristic == "h2":
            return self.h2(node)
        elif self.heuristic == "h3":
            return self.h3(node)
        #Default
        else:
            return self.h1(node)

#Used to calculate h1, the misplaced tiles heuristic
def hamming_distance(A, B):
    """Number of positions where vectors A and B are different."""
    return sum(a != b for a, b in zip(A, B))


def inversions(board):
    """The number of times a piece is a smaller number than a following piece."""
    return sum((a > b != 0 and a != 0) for (a, b) in combinations(board, 2))

#String printout of the board, swaps "0" with "_"
def board8(board, fmt=(3 * '{} {} {}\n')):
    """A string representing an 8-puzzle board"""
    return fmt.format(*board).replace('0', '_')


class Board(defaultdict):
    empty = '.'
    off = '#'

    def __init__(self, board=None, width=8, height=8, to_move=None, **kwds):
        if board is not None:
            self.update(board)
            self.width, self.height = (board.width, board.height)
        else:
            self.width, self.height = (width, height)
        self.to_move = to_move

    def __missing__(self, key):
        x, y = key
        if x < 0 or x >= self.width or y < 0 or y >= self.height:
            return self.off
        else:
            return self.empty

    def __repr__(self):
        def row(y): return ' '.join(self[x, y] for x in range(self.width))

        return '\n'.join(row(y) for y in range(self.height))

    def __hash__(self):
        return hash(tuple(sorted(self.items()))) + hash(self.to_move)


# A class that count the number of nodes visited to reach the destination
class CountCalls:
    """Delegate all attribute gets to the object, and count them in ._counts"""

    def __init__(self, obj):
        self._object = obj
        self._counts = Counter()

    def __getattr__(self, attr):
        "Delegate to the original object, after incrementing a counter."
        self._counts[attr] += 1
        return getattr(self._object, attr)


def report(searchers, problems, verbose=True):
    """Show summary statistics for each searcher (and on each problem unless verbose is false)."""
    for searcher in searchers:
        print(searcher.__name__ + ':')
        total_counts = Counter()
        for p in problems:
            prob = CountCalls(p)
            soln = searcher(prob)
            counts = prob._counts;
            counts.update(actions=len(soln), cost=soln.path_cost)
            total_counts += counts
            if verbose: report_counts(counts, str(p)[:40])
        report_counts(total_counts, 'TOTAL\n')


def report_counts(counts, name):
    """Print one line of the counts report."""
    print('{:9,d} nodes |{:9,d} goal |{:5.0f} cost |{:8,d} actions | {}'.format(
        counts['result'], counts['is_goal'], counts['cost'], counts['actions'], name))


############################################## Main Loop ######################################
#Dimensions of the board
rows = 3
columns = 3
#Generate a tuple with all 0's
puzzleBoard = (0 for i in range(rows * columns))

running = True
while (running):
    puzzleGenerated = False
    
    #Ask the user whether they would like to generate a random puzzle or input their own.
    print("Submit your own 8-puzzle? Y/N/E?")
    userInput = input()

    if (userInput == "Y"):
        #Get user input and verify that the input is correct
        print("Enter numbers separated by spaces (0 is the blank space): ")
        print("i.e. \"0 1 2 3 4 5 6 7 8\" will be")
        print("0  1  2")
        print("3  4  5")
        print("6  7  8")
        
        # Step 1: Take user input and convert it into a tuple of integers
        userInput = input()
        userInputTuple = tuple(map(int, userInput.split()))

        # Step 2: Copy the contents of userInputTuple into tempTuple
        tempTuple = tuple(userInputTuple)

        # Step 3: Sort tempTuple
        tempTuple = tuple(sorted(tempTuple))

        # Step 4: Check if tempTuple has 9 elements
        if len(tempTuple) == 9:
            # Step 5: Check if the next value is one greater than the current tuple value
            if all(tempTuple[i] + 1 == tempTuple[i + 1] for i in range(len(tempTuple) - 1)):
                #print("The tuple meets the criteria: It has 9 elements, and each element is one greater than the previous one.")
                puzzleGenerated = True
                puzzleBoard = userInputTuple                

            else:
                print("The tuple has 9 elements, but not every element is one greater than the previous one.")
                print("Duplicate values or values outside the range of 0 - 8")
                puzzleGenerated = False
        else:
            print("The tuple does not have 9 elements.")
            puzzleGenerated = False
        
        #print(str(userInputTuple))
        #print(str(tempTuple))

    elif (userInput == "N"):
        print("Generating 8-puzzle board")
        def is_solvable(puzzle):
            """Check if a given puzzle is solvable."""
            # Flatten the puzzle list and count inversions.
            inv_count = 0
            for i in range(8):
                for j in range(i + 1, 9):
                    if puzzle[i] > puzzle[j] and puzzle[j] != 0:
                        inv_count += 1
            # If the inversion count is even, the puzzle is solvable.
            return inv_count % 2 == 0
        
        def generate_puzzle():
            """Generate a random, solvable 8-puzzle."""
            while True:
                puzzle = random.sample(range(9), 9)  # Generate a random sequence of 9 numbers (0-8).
                if is_solvable(puzzle):
                    return tuple(puzzle)

        # Generate and store the puzzle in a tuple.
        puzzleBoard = generate_puzzle()
        
        puzzleGenerated = True
    
    elif (userInput == "E"):
        exit()        

    else:
        print("Please enter Y or N or E (for exit)")


    if (puzzleGenerated == True):
        #Print out the inital configuration
        print("The initial configuration is: ")
        
        #Print 8-puzzle
        print(puzzleBoard)

        print("Is this correct? Y/N")
        userInput = input()
        if (userInput == "N"):
            #Go back to the beginning
            continue      

        #For each of the 3 heuristics
        heuristics = ["misplacedRowsAndColumns", "misplacedTiles", "manhattenDistance"]
        for heuristic in heuristics:
            print("")
            print("A* using the following heuristic: " + heuristic)
            
            #Makes a 8-puzzle with the given initial board configuration
            try:
                problem = EightPuzzle(puzzleBoard)
            except:
                print("The given initial configuration can't be solved by A*, it would require the heuristic getting worse before it finds a solution.")
                print("")
                continue
            
            if heuristic == "misplacedTiles":
                problem.setHeuristic("h1")
            elif heuristic == "manhattenDistance": 
                problem.setHeuristic("h2")
            else:
                problem.setHeuristic("h3")
                
            #Start tracking metrics
            startTime = time.time()
            tracemalloc.start()     #Track memory usage
            
            #Apply the A* algorithm and print out all the states the algorithm took to go from the start state to the goal state
            for state in path_states(astar_search(problem)):
                print(board8(state))
                
            print("")
            
            #Stop tracking metrics and print out results
            print("(Current Memory Usage, Peak Memory Usage)")
            print(tracemalloc.get_traced_memory())
            print("")
            tracemalloc.stop()
            
            endTime = time.time()
            elaspedTime = endTime - startTime
            print("Elapsed time: " + str(elaspedTime))
            print("")

            #Prints out the total nodes visited for the problem
            print(report([astar_search], [problem]))
