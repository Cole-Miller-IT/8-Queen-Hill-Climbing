#Program to solve the 8-puzzle problem using heuristics and the A* algorithm
#H1 is the amount of misplaced tiles
#H2 is the Manhatten distance 
#H3 is the sum of tiles misplaced rows and columns

################ Main Program ##########################
from ast import Constant
from calendar import c
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

BOARDSIZE = 8

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


def hillClimbRandomRestartFirstChoice(problem):
    currentNode = Node(problem.initial)
    maxRestarts = 100
    
    searching = True
    while(searching):
        print("The current board state is: ")
        PrintBoard(currentNode.state)
        
        #if we found a board with no queens attacking eachother (a goal state)
        if problem.reachedGoal(currentNode.state):
            print("reached goal")
            print("remaining restarts: " + str(maxRestarts))
            searching = False
            return currentNode
        
        #If the program wasn't able to find a solution in time
        elif maxRestarts < 0:
            print("Ran out of restarts")
            print("Final board state is: ")
            PrintBoard(currentNode.state)
            searching = False
            return currentNode

        #Search for the next move to take
        else:
            board = currentNode.state.copy() #Get a deep copy of the board state to calculate the next states on
            
            #Generate all potential next states. So each queen can move to one of the other 7 empty spaces in its column and this is done for every one of the 8 queens
            #so there are 8 * 7 = 56 possible next states to calculate     pg. 112 of the text book
            breakOut = False #Used to get out of the nested loops if a better heuristic is found
            column = 0
            for queensValue in board:
                #print("\nQueen's original column: " + str(column) + "")
                #print("Queen's original row: " + str(queensValue))
                
                #generate all states for the other 7 spaces
                for row in range(0,8):
                    #print("rand row " + str(row))
                    if (row == queensValue):
                        pass
                        #this is where the queen currently is
                        #print("Skipping row " + str(row) + " (current queen position)\n")
                    else:
                        #Generate the board if the current queen were to move into this row
                        backupRow = queensValue
                        board[column] = row
                        
                        #print("Queen's new row: " + str(row))
                        #print("The future board state is: ")
                        #PrintBoard(board)

                        #calculate the heuristic on this new board state (num of attacking queens)
                        nextHeuristicValueFound = problem.checkQueenConflicts(board)  
                        #print("Number of conflicts for future board state is: " + str(nextHeuristicValueFound))

                        ####First choice starts here###
                        #if the next board state found has a better heuristic value than the current state, take it 
                        currentHeuristicValue = problem.checkQueenConflicts(currentNode.state) 
                        if nextHeuristicValueFound < currentHeuristicValue:
                            #print()
                            print("better board state found")
                            print(nextHeuristicValueFound)
                            
                            #Move the queen to the better position
                            currentNode.state[column] = row
                            breakOut = True #maybe I could design this better but I didn't want to completelty rewritethe code I had
                            break
                        
                        else:
                            #undo the change above the board state
                            board[column] = backupRow
                  
                if (breakOut == True):
                    break                    

                column = column + 1   
                
            if (breakOut == True):
                continue
                
            #if you reached here then none of the possible moves resulted in a better heuristic
            #restart the search from a random board state
            print("no moves were better, restarting ")
            currentNode.state, maxRestarts = restart(maxRestarts)
                



def hillClimbRandomRestart(problem):
    currentNode = Node(problem.initial)
    maxRestarts = 100
    
    searching = True
    while(searching):
        print("The current board state is: ")
        PrintBoard(currentNode.state)
        
        #if we found a board with no queens attacking eachother (a goal state)
        if problem.reachedGoal(currentNode.state):
            print("reached goal")
            print("remaining restarts: " + str(maxRestarts))
            searching = False
            return currentNode
        
        #If the program wasn't able to find a solution in time
        elif maxRestarts < 0:
            print("Ran out of restarts")
            print("Final board state is: ")
            PrintBoard(currentNode.state)
            searching = False
            return currentNode

        #Search for the next move to take
        else:
            board = currentNode.state.copy() #Get a deep copy of the board state to calculate the next states on
            
            #Make a 2D array to store all of the heuristics values (number of conflicts) to determine what move will be the best
            w, h = BOARDSIZE, BOARDSIZE
            heuristicsBoard = [[-1 for x in range(w)] for y in range(h)]

            #Generate all potential next states. so each queen can move to one of the other 7 empty spaces in its column and this is done for every one of the 8 queens
            #so there are 8 * 7 = 56 possible next states to calculate     pg. 112 of the text book
            column = 0
            for queensValue in board:
                #print("\nQueen's original column: " + str(column) + "")
                #print("Queen's original row: " + str(queensValue))
                
                #generate all states for the other 7 spaces
                for row in range(0,8):
                    #print("rand row " + str(row))
                    if (row == queensValue):
                        #this is where the queen currently is
                        #print("Skipping row " + str(row) + " (current queen position)\n")
                        heuristicsBoard[column][row] = 99 #current position
                    else:
                        #Generate the board if the current queen were to move into this row
                        backupRow = queensValue
                        board[column] = row
                        
                        #print("Queen's new row: " + str(row))
                        #print("The future board state is: ")
                        #PrintBoard(board)

                        #calculate the heuristic on this new board state (num of attacking queens)
                        result = problem.checkQueenConflicts(board)  
                        #print("Number of conflicts for future board state is: " + str(result))

                        #store this value for later
                        heuristicsBoard[column][row] = result

                        #undo the change above the board state
                        board[column] = backupRow
                        
                column = column + 1


            #Determine which is the best (least amount of conflicts neighbor) to take
            #print("Heuristics board: ")
            #for row in heuristicsBoard:
                #print(str(row))

            def transpose(board):
                return [[board[j][i] for j in range(len(board))] for i in range(len(board[0]))]
            
            print()
            transposed = transpose(heuristicsBoard)
            print("Heuristics board: ")
            for row in transposed:
                    print(str(row))
                    
            #Takes the heuristics board and finds move(s) that gives the lowest heuristic 
            def getBestNeighbors(board):
                bestMoves = []     
                bestHeuristic = 99

                row = 0
                for moves in board:
                    #print()
                    #print("Heuristics for queens row " + str(row) + ": ")
                    #print(moves)
                    column = 0
                    for move in moves:
                        #print(move)
                        if move < bestHeuristic:
                            #found a new move with the lowest heuristic
                            #print("New best or current heuristic found: " + str(move))
                            bestHeuristic = move
                            bestMoves = [] #Clear the array of any previous values
                            bestMoves.append([row,column])
                            
                        elif move == bestHeuristic:
                            #found a new move with the same heuristic
                            bestMoves.append([row,column])
                            
                        column = column + 1
                            
                    row = row + 1
                    
                print()
                print("Best Heuristic found was: " + str(bestHeuristic))
                return (bestMoves, bestHeuristic)
                        
              
                
            bestMovesFound, bestHeuristicValueFound = getBestNeighbors(transposed)
            print()
            print("Best move(s) found: (row, column)")
            print(str(bestMovesFound))
            
            #if all neighbors are worse or the same (>=) to the current node then we have hit a local minimum   
            currentHeuristicValue = problem.checkQueenConflicts(currentNode.state) 
            if bestHeuristicValueFound >= currentHeuristicValue:
                print()
                print("local minimum found")
                print("number of conflicts: " + str(currentHeuristicValue))   
                    
                #Restart from a new board state
                currentNode.state, maxRestarts = restart(maxRestarts)
                
                #searching = False
                #return currentNode
                #return currentNode 

            else:
                row = -1
                column = -1
                #choose which move to make
                if len(bestMovesFound) == 1:
                    print()
                    print("Single move")
                    #only one move found
                    row = bestMovesFound[0][0]
                    column = bestMovesFound[0][1]
                    #print(row)
                    #print(column)
                    currentNode.state[column] = row
                else:
                    print()
                    print("multiple moves move")
                    #Randomly choose between the best moves
                    randomIndex = random.randint(0, len(bestMovesFound) - 1)

                    row = bestMovesFound[randomIndex][0]
                    column = bestMovesFound[randomIndex][1]
                    #print(row)
                    #print(column)
                    currentNode.state[column] = row
                    
                #currentNode.state[0] = 0
                print()
                print("Moving queen " + str(column) + " to row " + str(row))
                #print("next board state")
                #PrintBoard(currentNode.state)
                #result = problem.checkQueenConflicts(currentNode.state)
                #print(str(result))
                
            #searching = False
            #return currentNode
            
            


#The 8-Queen problem class that contains the heuristics, actions, goal state, etc..
class EightQueen(Problem):
    #Arrange 8 queens so that none of them are attacking eachother on an 8x8 chess board

    def __init__(self, initial):
        self.initial = initial

    #Returns the amount of conflicts/attacks between all of the queens on the board
    def checkQueenConflicts(self, board):
        result = 0
        # Check all of the 8 queens for conflicts, going left to right
        for column1 in range(len(board)):
            for column2 in range(column1 + 1, len(board)):
                # Get the row positions for the two queens
                row1 = board[column1]
                row2 = board[column2]
            
                #Check horizontal conflicts
                if row1 == row2:
                    #print("\nComparing Queen at Column: " + str(column1) + ", Row: " + str(row1) + " with Queen at Column: " + str(column2) + ", Row: " + str(row2))
                    #print("Horizontal conflict detected")
                    result += 1

                # Check diagonal conflicts
                if abs(column1 - column2) == abs(row1 - row2):
                    #print("\nComparing Queen at Column: " + str(column1) + ", Row: " + str(row1) + " with Queen at Column: " + str(column2) + ", Row: " + str(row2))
                    #print("Diagonal conflict detected")
                    result += 1
                        
        return result
        

    
    #Checks if the board contains any conflicts
    def reachedGoal(self, board):
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
        
#Generate a new random board state for the 8-queen problem. array index = queen's column   and   array value = queen's row
def generateRandomBoard():
    board = [random.randint(0,7) for x in range(8)]
    return board


def restart(maxRestarts):  
    #implment random restart here and decrement maxRestarts if the maxConflicts is not 0 (i.e. not at a goal state)          
    maxRestarts = maxRestarts - 1
                
    newBoard = generateRandomBoard()
    #print("New board: ")
    #print(newBoard)
    
    return (newBoard, maxRestarts)
    

############################################## Main Loop ######################################
running = True
while (running):
    #Create a random board state for 8-Queen problem. ##static for testing
    board = [1, 2, 3, 1, 5, 4, 0, 7]
    noConflictsBoard = [0, 6, 3, 5, 7, 1, 4, 2]
    
    #initalize the problem
    #e1 = EightQueen(board)
    #print("The initial board is: ")
    #PrintBoard(e1.initial)
    
    
    #perform the hill climbing algorithm on the problem
    #solution = hillClimbRandomRestart(e1)
    #print("The solution is: ")
    #PrintBoard(solution.state)


    #####first choice hill climbing########
    e2 = EightQueen(board)
    solution = hillClimbRandomRestartFirstChoice(e2)
    
    running = False
