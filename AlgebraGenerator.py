import itertools
import time, sys
from datetime import datetime

# Four atoms. 
atoms = ['a','b','c','d']
# If the identity is atomic it will be represented by 'a'. 
# This fixes the left-most column and uppermost row of the composition table of atoms.
# A fixed entry is represented by a consistent triple, eg. ('a','a','a') or ('a','b','b').
def atomicIdentity(nAtoms):
    atoms = [chr(i + 97) for i in range(nAtoms)]
    return [('a', atom, atom) for atom in atoms] + [(atom, 'a', atom) for atom in atoms[1:]]

# Suppose that the identity element consists of nAtoms, with nAtoms > 1.
# This construction assumes that the identity fragments form the first nFragments
# atoms, ie. a three-fragment identity will be the union of a, b and c.
def fragmentIdentity(nAtoms, nFragments):
    if nFragments == 1:
        return atomicIdentity(nAtoms)
    else:
        atoms = [chr(i + 97) for i in range(nAtoms)]
        return([(atom, atom, atom) for atom in atoms[:nFragments]] + 
            [(atom1, atom2, 0) for atom1, atom2 in itertools.product(atoms[:nFragments], repeat=2) if atom1 != atom2])

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
def genCyclePartition(converse, nAtoms):
    atoms = [chr(i + 97) for i in range(nAtoms)]
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
def createnAtomAlgebraFromCycles(cycles, converse, nAtoms):
    # Create an empty atomTable
    atomTable = [[set() for i in range(nAtoms)] for j in range(nAtoms)]
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
# We can also specify that the identity size should be fixed, so that the number
# of atoms in the identity of the first algebra (the simples)
def generateAlgebrasFromFixedEntries(entriesToFix, converse, nAtoms, fixIdentitySize = False):
    # First generate all of the cycles from the desired converse structure.
    cycles = genCyclePartition(converse, nAtoms)
    # Then generate the necessary, forbidden and optional cycles fixing the desired entries.
    necessaryCycles, forbiddenCycles, optionalCycles = fixEntries(entriesToFix, cycles)
    # Take the powerset of optional cycles. This is the set of choices of optional cycles to include.
    pset = [combinations(optionalCycles, n) for n in range(len(optionalCycles)+1)]
    pset = list(chain.from_iterable(pset))
    pset = [list(c) for c in pset]
    # Add the necessary cycles to every choice of optional cycles. Each possible cycle set is an algebra.
    possibleCyclesets = [necessaryCycles + choice for choice in pset]
    algebras = []
    nCyclesets = len(possibleCyclesets)
    for cycleset in possibleCyclesets:
        newAlgebra = createnAtomAlgebraFromCycles(cycleset, converse, nAtoms)
        # We're only interested in nonassociative algebras
        validAlgebra = newAlgebra.isNA()
        if validAlgebra: # check for isomorphisms
            for algebra in algebras:
                if newAlgebra.isIsomorphic(algebra, returnIsomorphism = False):
                    validAlgebra = False
                    # If an isomorphic algebra is found, we don't need to check the rest.
                    break
        if fixIdentitySize and validAlgebra: # If we want to fix the size of the identity
            if len(algebras) == 0:
                fixedIdentitySize = len(newAlgebra.identity)
            else:
                validAlgebra = (len(newAlgebra.identity) == fixedIdentitySize)
        if validAlgebra: algebras.append(newAlgebra)
    return algebras

    # We may want to build in an assumption that any element not specified in 
    # the converse structure is assumed to be symmetric. To prepare for this,
    # we calculate the number of symmetric atoms based on the number of
    # non-symmetric atoms.
def generateAlgebrasFromIdentityAndConverse(nAtoms, identitySize, converse):
    numberSymmetric = nAtoms - len([k for k in converse.keys() if converse[k] != k])
    creationStatement = "Generating " + str(nAtoms) + "-atom algebras with "
    if identitySize == 1: 
        creationStatement += "atomic identity "
    else:
        creationStatement += str(identitySize) + "-fragment identity "
    creationStatement += ("and " + str(numberSymmetric) + " symmetric atom" + 
                          (numberSymmetric != 1)*"s" + ".")
    print(creationStatement)
    algebras = generateAlgebrasFromFixedEntries(
            fragmentIdentity(nAtoms, identitySize), 
            converse = converse, nAtoms = nAtoms, fixIdentitySize = True)
    outcomeStatement = ("Found " + str(len(algebras)) + 
                             " non-isomorphic algebra" + 
                             (len(algebras) > 1) * "s" + ".")
    print(outcomeStatement)
    return algebras

def conversesRespectingIdentity(nAtoms, identitySize):
    converses = []
    for numberSymmetric in [i for i in range(identitySize, nAtoms + 1) if (nAtoms - i) % 2 == 0]:
        numberNonSymmetric = nAtoms - numberSymmetric
        converse = [(chr(i + 97), chr(i + 97)) for i in range(numberSymmetric)]
        for conversePairStart in [numberSymmetric + j for j in range(numberNonSymmetric) if j % 2 == 0]:
            converse.append((chr(conversePairStart + 97), chr(conversePairStart + 97 + 1)))
        converses.append(AtomicAlgebra.conversePairsToDict(converse))
    return converses

def generateAlgebras(nAtoms):
    algebras = []
    for identitySize in range(1, nAtoms + 1):
        for converse in conversesRespectingIdentity(nAtoms, identitySize):
            algebras += generateAlgebrasFromIdentityAndConverse(nAtoms, identitySize, converse)
    return(algebras)








