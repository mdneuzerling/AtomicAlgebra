import itertools
import time, sys
from datetime import datetime

# Four atoms. 
atoms = ['a','b','c','d']
# If the identity is atomic it will be represented by 'a'. 
# This fixes the left-most column and uppermost row of the composition table of atoms.
# A fixed entry is represented by a consistent triple, eg. ('a','a','a') or ('a','b','b').
atomicIdentity = [('a', atom, atom) for atom in atoms] + [(atom, 'a', atom) for atom in atoms[1:]]
# The identity can also be a union of atoms. Here we consider two atoms, assumed 'a' and 'b', unioning to identity.
twoFragmentIdentity = [(atom, atom, atom) for atom in atoms[:2]] + [(atom1, atom2, 0) for atom1, atom2 in itertools.product(atoms[:2], repeat=2) if atom1 != atom2]
# Here we consider three atoms, assumed 'a', 'b' and 'c', unioning to identity.
threeFragmentIdentity = [(atom, atom, atom) for atom in atoms[:3]] + [(atom1, atom2, 0) for atom1, atom2 in itertools.product(atoms[:3], repeat=2) if atom1 != atom2]
# Here we consider four atoms unioning to identity.
fourFragmentIdentity = [(atom, atom, atom) for atom in atoms] + [(atom1, atom2, 0) for atom1, atom2 in itertools.product(atoms, repeat=2) if atom1 != atom2]
# All 10 possible converse structures.
# We don't actually need all 10. We only need to consider 3 cases: 
    # All self-converse.
    # Just 2 self-converse.
    # No self-converse.
# All others will be isomorphic 
converses = [
        {'a': 'a', 'b': 'b', 'c': 'c', 'd': 'd'}, # all self-converse
        {'a': 'b', 'b': 'a', 'c': 'c', 'd': 'd'}, # c,d self-converse, (a,b)
        {'a': 'a', 'b': 'c', 'c': 'b', 'd': 'd'}, # a,d self-converse, (b,c)
        {'a': 'a', 'b': 'b', 'c': 'd', 'd': 'c'}, # a,b self-converse, (c,d)
        {'a': 'c', 'b': 'b', 'c': 'a', 'd': 'd'}, # b,d self-converse, (a,c)
        {'a': 'a', 'b': 'd', 'c': 'c', 'd': 'b'}, # a,c self-converse, (b,d)
        {'a': 'd', 'b': 'b', 'c': 'c', 'd': 'a'}, # b,c self-converse, (a,d)
        {'a': 'b', 'b': 'a', 'c': 'd', 'd': 'c'}, # (a,b), (c,d)
        {'a': 'd', 'b': 'c', 'c': 'b', 'd': 'a'}, # (a,d), (b,c)
        {'a': 'c', 'b': 'd', 'c': 'a', 'd': 'b'}  # (a,c), (b,d)
        ]

# Given a triple and a converse structure, generate the cycle including that triple.
# This is an implementation of the relation algebra concept of a Peircean transform.
# Cycle generated by (x,y,z) is:
    # [ (x,y,z), (con(x),z,y), (y,con(z),con(x)),
    #   (con(y),con(x),con(z)),(con(z),x,con(y)), (z,con(y),x) ]
# A triple in a cycle is consistent if and only if all triples in the cycle are consistent.
def genCycle(triple, converse):
    x, y, z = triple
    cycle = []
    cycle.append(triple)
    cycle.append((converse[x], z, y))
    cycle.append((y, converse[z], converse[x]))
    cycle.append((converse[y], converse[x], converse[z]))
    cycle.append((converse[z], x, converse[y]))
    cycle.append((z, converse[y], x))
    cycle.sort()
    # Remove duplicates.
    return list(set(cycle))

# Given a converse structure, partition the triples of elements into cycles.
def genCyclePartition(converse):
    parts = []
    for triple in itertools.product(atoms, repeat = 3):
        cycle = genCycle(triple, converse)
        if cycle not in parts: parts.append(cycle)
    return parts
    
# Fix an entry of an atom table to either a single atom or 0.
# Input is a list of tuples of fixed entries, eg. [('a','a','b')] will fix the 
# upper-left entry to 'b' and only 'b'. Output is a list of necessary cycles, a 
# list of forbidden cycles, and a list of optional (remaining) cycles. Any 
# algebra with consistent cycles including at least those that are necessary, 
# and none of those that are forbidden, will have the desired fixed entry.
def fixEntries(entriesToFix, cycles):
    cyclesToSort = cycles
    necessaryCycles = []
    forbiddenCycles = []
    # a, b, c in entriesToFix means that a;b = c is the composition we want to fix.
    for a, b, c in entriesToFix:
        # If c == 0, then a;b composes to nothing.
        if c == 0:
            for cycle in cyclesToSort:
                if (a,b) in [triple[:2] for triple in cycle]:
                    if cycle not in forbiddenCycles: forbiddenCycles.append(cycle)
        else:
            for cycle in cyclesToSort:
                # If the cycle contains a;b composing to c, it is necessary.
                if (a,b,c) in cycle:
                    if cycle not in necessaryCycles: necessaryCycles.append(cycle)
                # If the cycle contains a;b composing to something other than c, it is forbidden.
                elif (a,b) in [triple[:2] for triple in cycle]:
                    if cycle not in forbiddenCycles: forbiddenCycles.append(cycle)
    # A cycle that is neither necessary or forbidden is optional.
    optionalCycles = [cycle for cycle in cycles if cycle not in necessaryCycles and cycle not in forbiddenCycles]
    return necessaryCycles, forbiddenCycles, optionalCycles

# Create an algebra from a list of cycles to be included, and a converse structure.
# First creates an atom table from the cycles, then creates an instance of the AtomicAlgebra class
def create4AtomAlgebraFromCycles(cycles, converse):
    # Create an empty atomTable
    atomTable = [[set() for i in range(4)] for j in range(4)]
    # Fill the atom table.
    for cycle in cycles:
        for triple in cycle:
            x, y, z = triple
            rowPos = ord(x) - 97
            colPos = ord(y) - 97
            # For every triple in every cycle, set the relevant entry of the atomTable to correspond to the cycle.
            atomTable[rowPos][colPos] = atomTable[rowPos][colPos].union(set([z]))
    newAlgebra = AtomicAlgebra(atomTable, converse)
    return newAlgebra

# Generate a list of nonassociative algebras with an atomTable with desired fixed entries and converse structure.
# Returned list contains no two isomorphic algebras.
def generateAlgebrasFromFixedEntries(entriesToFix, converse):
    # First generate all of the cycles from the desired converse structure.
    cycles = genCyclePartition(converse)
    # Then generate the necessary, forbidden and optional cycles fixing the desired entries.
    necessaryCycles, forbiddenCycles, optionalCycles = fixEntries(entriesToFix, cycles)
    # Take the powerset of optional cycles. This is the set of choices of optional cycles to include.
    pset = [combinations(optionalCycles, n) for n in range(len(optionalCycles)+1)]
    pset = list(chain.from_iterable(pset))
    pset = [list(c) for c in pset]
    # Add the necessary cycles to every choice of optional cycles. Each possible cycle set is an algebra.
    possibleCyclesets = [necessaryCycles + choice for choice in pset]
    algebras = []
    # The counter is used to track progress and display a progress bar.
    counter = 1
    nCyclesets = len(possibleCyclesets)
    for cycleset in possibleCyclesets:
        newAlgebra = create4AtomAlgebraFromCycles(cycleset, converse)
        validAlgebra = True
        # We're only interested in nonassociative algebras
        if not newAlgebra.isNA(): 
            validAlgebra = False
        # Strictly speaking, we don't need to separate the cases in which 
        # the identity is two, three, or four fragments.
        elif entriesToFix == twoFragmentIdentity and len(newAlgebra.identity) > 2:
            validAlgebra = False
        elif entriesToFix == threeFragmentIdentity and len(newAlgebra.identity) > 3:
            validAlgebra = False
        else:
            # Check to see if the new algebra is isomorphic to an algebra we have already constructed.
            for algebra in algebras:
                if newAlgebra.isIsomorphic(algebra, returnIsomorphisms = False, creating4AtomAlgebras = True):
                    validAlgebra = False
                    # If an isomorphic algebra is found, we don't need to check the rest.
                    break
        # If the algebra is valid, add it to the list of algebras.
        if validAlgebra: algebras.append(newAlgebra)
    return algebras

def gen4Atoms():
    # Generate all algebras and report on progress along the way.
    # We generate the algebras in 6 cases according to identity and converse structure.
    # This reduces the number of isomorphism checks needed.
    algebras = []
    print("Generating 4 atom algebras with two-fragment identity, all atoms self-converse.")
    algebras1 = generateAlgebrasFromFixedEntries(twoFragmentIdentity, converses[0])
    print("Found " + str(len(algebras1)) + " non-isomorphic algebra" + (len(algebras1) > 1) * "s" + ".")
    print("Generating 4 atom algebras with two-fragment identity, only 2 atoms self-converse.")
    algebras2 = generateAlgebrasFromFixedEntries(twoFragmentIdentity, converses[3])
    print("Found " + str(len(algebras2)) + " non-isomorphic algebra" + (len(algebras2) > 1) * "s" + ".")
    print("Generating 4 atom algebras with three-fragment identity, all atoms self-converse.")
    algebras3 = generateAlgebrasFromFixedEntries(threeFragmentIdentity, converses[0])
    print("Found " + str(len(algebras3)) + " non-isomorphic algebra" + (len(algebras3) > 1) * "s" + ".")
    print("Generating 4 atom the algebra with four-fragment identity.")
    algebras4 = generateAlgebrasFromFixedEntries(fourFragmentIdentity, converses[0])
    print("Found " + str(len(algebras4)) + " non-isomorphic algebra" + (len(algebras4) > 1) * "s" + ".")
    print("Generating 4 atom algebras with atomic identity, all atoms self-converse.")
    algebras5 = generateAlgebrasFromFixedEntries(atomicIdentity, converses[0])
    print("Found " + str(len(algebras5)) + " non-isomorphic algebra" + (len(algebras5) > 1) * "s" + ".")
    print("Generating 4 atom algebras with atomic identity, only 2 atoms self-converse.")
    algebras6 = generateAlgebrasFromFixedEntries(atomicIdentity, converses[3])
    print("Found " + str(len(algebras6)) + " non-isomorphic algebra" + (len(algebras6) > 1) * "s" + ".")
    return algebras1 + algebras2 + algebras3 + algebras4 + algebras5 + algebras6
    
