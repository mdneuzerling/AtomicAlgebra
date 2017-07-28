#example = "[[a,b,c,d],[b,a,0,0],[c,0,0,a],[d,0,a,0]]"
#atomTable = AtomicAlgebra._stringToAtomTable(example)
#nAtoms = len(atomTable[0])
#atoms = [set([chr(i + 97)]) for i in range(nAtoms)]
#examplePairs = [('a','a'), ('b','b'), ('c', 'd')]
#x = AtomicAlgebra(example, examplePairs)

from functools import reduce
from itertools import chain, combinations, product, permutations

# This class is used to represent and examine algebras on atom tables.
# It is intended to be used for nonassociative algebras, but this is not assumed.
class AtomicAlgebra:
    
    # Create an algebra from a table of atoms, which gives compositions, and a converse structure.
    # An atom table is a list of lists, with each entry a set (as distinct from set) of atoms.
    # The set of atoms is interpreted as a union. Atoms are 'a', 'b', 'c', etc.
    # The converse pair is a list of 2-tuples of atoms.
    # If 'a' is converse to 'b', write as ('a','b').
    # If 'a' is symmetric, write as ('a', 'a').
    # Can also give converses as a dictionary.
    # Algebra may not necessarily meet all the axioms.
    def __init__(self, atomTable, conversePairs = None):
        if type(atomTable) == str:
            atomTable = self._stringToAtomTable(atomTable)
        self.nAtoms = len(atomTable[0])
        self.atoms = [set([chr(i + 97)]) for i in range(self.nAtoms)]
        self.atomTable = atomTable
        # If no converses given assume all atoms are symmetric.
        if conversePairs == None: 
            self.conversePairs = [(x,x) for x in [chr(i + 97) for i in range(self.nAtoms)]]
        # Can also give converses as a dictionary.
        elif type(conversePairs) == dict:
            self.conversePairs = []
            for pair in conversePairs.items():
                if pair not in self.conversePairs and pair[::-1] not in self.conversePairs:
                    self.conversePairs.append(pair)
        else:
            self.conversePairs = conversePairs
        # set up the basic properties of the algebra.
        self._nonIdentityAtoms = None
        self.top = functools.reduce(lambda x, y : x |y, self.atoms)
        self.zero = set()
        # need to define elements as power set of atoms
        # Combinations seems to be Sage only. Need to get a power set somehow.
        self.elements = [combinations(list(self.top), n) for n in range(self.nAtoms+1)]
        self.elements = list(chain.from_iterable(self.elements))
        self.elements = [set(element) for element in self.elements]
        self.nElements = 2**self.nAtoms 
        self.nNonZeroElements = self.nElements - 1
        # We may want to call on a converse from a dictionary.
        # So here we construct a dictionary of converses from the converse pairs.
        self.atomConverses = dict()
        for conversePair in self.conversePairs:
            if conversePair[0] == conversePair[1]: # symmetric atom
                self.atomConverses[conversePair[0]] = conversePair[0]
            else: # non-symmetric atoms
                self.atomConverses[conversePair[0]] = conversePair[1]
                self.atomConverses[conversePair[1]] = conversePair[0]
        self._identity = None
        self._semigroup = None
        # properties
        self._isNA = None
        self._satisfiesWAaxiom = None
        self._isWA = None
        self._satisfiesSAaxiom = None
        self._isSA = None
        self._isAssociative = None
        self._isRA = None
        self._consistentAtomTriples = None
        self._consistentMirrorFreeAtomTriples = None
        self._isRepresentable = None
        self._representation = None

    # A human-readable description of each relation algebra axiom.
    AXIOMS = {
        "R01": "+-commutativity: x + y = y + x",
        "R02": "+-associativity: x + (y + z) = (x + y) + z",
        "R03": "Huntington's axiom: -(-x + -y) + -(-x + y) = x",
        "R04": ";-associativity: x;(y;z) = (x;y);z",
        "R05": ";-distributivity: (x + y);z = x;z + y;z",
        "R06": "identity law: x;1' = x",
        "R07": "converse-involution: con(con(x)) = x",
        "R08": "converse-distributivity: con(x + y) = con(x) + con(y)",
        "R09": "converse-involutive distributivity: con(x;y) = con(y);con(x)",
        "R10": "Tarski/De Morgan axiom: con(x); -(x;y) + -y = y", 
        "WA" : "((id . x) . top) . top = (id . x) . (top . top)",
        "SA" : "(x . top) . top = x . (top . top)"
    }           

    # Given an atom table as a string, convert it to a matrix (list of lists).
    # Fuck me, change this.
    # Also strip spaces in the input string
    @staticmethod
    def _stringToAtomTable(matrixString):
        M1 = matrixString.strip()[1:-1]
        M2 = M1.strip()[1:-1]
        M3 = [line.split(',') for line in M2.split('],[')]
        M4 = [[set(entry.split("+"))-set(['0']) for entry in line] for line in M3]
        return M4  

    # Give a human readable report on a list of failed axioms, eg. ["R01", "R02", "R07"].
    # This only works on a list of axioms. How do we get it to work for
    # singletons too?
    @staticmethod
    def reportFailedAxioms(failedAxioms):
        if type(failedAxioms) is not list: failedAxioms = [failedAxioms]
        for axiom in failedAxioms:
            print("Fails axiom " + axiom + ": " + AtomicAlgebra.AXIOMS[axiom] + ".")
            
     # Given a map between atoms as a dictionary, returns a map that works on unions of atoms.
    @staticmethod
    def atomFunction(atomMap, element):
        if type(element) is str:
            return atomMap[element]
        else:
            return set([AtomicAlgebra.atomFunction(atomMap, x) for x in element])
        
    # Check if a map between atom structures preserves composition.
    # This is required for the function to be an isomorphism.
    def preservesComposition(self, algebra2, atomMap):
        preservesComposition = True
        for x, y in itertools.product(self.atoms, repeat = 2):
            if AtomicAlgebra.atomFunction(atomMap, self.compose(x, y)) != algebra2.compose(AtomicAlgebra.atomFunction(atomMap, x), AtomicAlgebra.atomFunction(atomMap, y)):
                preservesComposition = False
                break
        return preservesComposition

    # Checks if a given algebra is isomorphic to self.
    # If creating4AtomAlgebras, we're assuming that our algebras are coming from the gen4Atoms function.
    # If so, we can assume some additional structure about the converses.
    # This isn't necessary, but it does speed up the isomorphism checking.
    # Can also return a list of isomorphisms, but this takes a long time.
    def isIsomorphic(self, algebra2, returnIsomorphisms = False, creating4AtomAlgebras = False):
        # First we check that the algebras are the same size.
        # This is a necessary condition for isomorphism, so can save some time.
        if self.nAtoms != algebra2.nAtoms:
            return False
        # Next we check that the converse pairs match in number and structure.
        # This is a necessary condition for isomorphism, so can save some time.
        converses1 = self.conversePairs
        nonSelfConversePairs1 = len(converses1)
        selfConverses1 = [x[0] for x in converses1 if x[0] == x[1]]
        nonSelfConversePairs1 = [x for x in converses1 if x[0] != x[1]]
        converses2 = algebra2.conversePairs
        nonSelfConversePairs2 = len(converses2)
        selfConverses2 = [x[0] for x in converses2 if x[0] == x[1]]
        nonSelfConversePairs2 = [x for x in converses2 if x[0] != x[1]]
        if len(selfConverses1) != len(selfConverses2):
            return False
        # Enumerate all possible functions respecting converse
        # First we check if we are creating4AtomAlgebras, so we might make 
        # additional assumptions. These assumptions speed up the isomorphism
        # checking significantly. In particular, we can assume the 'a' is an 
        # identity element, and that either all atoms are symmetric or that the
        # only converse pair is ('c','d').
        # Note the small number of possible converse structures.
        if creating4AtomAlgebras and self.identity == set(['a']) and algebra2.identity == set(['a']):
            if len(selfConverses1) == 4:
                possibleIsomorphisms = [
                    {'a': 'a', 'b': 'c', 'c': 'b', 'd': 'd'},
                    {'a': 'a', 'b': 'b', 'c': 'd', 'd': 'c'},
                    {'a': 'a', 'b': 'd', 'c': 'c', 'd': 'b'},
                    {'a': 'a', 'b': 'c', 'c': 'd', 'd': 'b'},
                    {'a': 'a', 'b': 'd', 'c': 'b', 'd': 'c'}
                    ]
            elif len(selfConverses1) == 2:
                possibleIsomorphisms = [
                    {'a': 'a', 'b': 'b', 'c': 'c', 'd': 'd'},
                    {'a': 'a', 'b': 'b', 'c': 'd', 'd': 'c'},
                    ]
            else:
                raise ValueError("Unexpected converse structure. Assumes either all atoms are symmetric, or only converse pair is ('c','d').")
        # If we are not creating4AtomAlgebras, then we must check for 
        # isomorphisms by brute force.
        else:
            # First enumerate all possible ways to map symmetric atoms from 
            # the first algebra to self converse atoms from the second algebra.
            possibleSelfConverseMaps = []
            for perm in permutations(selfConverses2):
                possibleSelfConverseMaps.append(zip(selfConverses1, perm))
            possibleSelfConverseMaps = [list(p) for p in possibleSelfConverseMaps]
            #return(possibleSelfConverseMaps)
            # Now enumerate all possible ways to map converse pairs from the 
            # first algebra to converse pairs from the second algebra.
            possibleConversePairMaps = []
            for perm1 in list(product(*[[x,x[::-1]] for x in nonSelfConversePairs2])):
                for perm2 in permutations(perm1):
                    map = []
                    pairing = zip(nonSelfConversePairs1, perm2)
                    for pair in pairing:
                        map.append((pair[0][0], pair[1][0]))
                        map.append((pair[0][1], pair[1][1]))
                    possibleConversePairMaps.append(map)
            # Now combine them to generate all maps respecting the converse structure.
            possibleIsomorphisms = []
            for selfConverseMap, conversePairMap in itertools.product(possibleSelfConverseMaps, possibleConversePairMaps):
                possibleIsomorphisms.append(selfConverseMap + conversePairMap)
            possibleIsomorphisms = [dict(x) for x in possibleIsomorphisms]
        # Assume that the algebras are not isomorphic.
        areIsomorphic = False
        isomorphisms = []
        # Go through all the maps that preserve converse structure to test if
        # they also preserve composition. If so, they are isomorphic.
        # If we want to enumerate all isomorphisms, check all maps.
        # Otherwise, break if an isomorphism is found, to save time.
        for possibleIsomorphism in possibleIsomorphisms:
            if self.preservesComposition(algebra2, possibleIsomorphism):
                areIsomorphic = True
                if not returnIsomorphisms:
                    break
                else:
                    isomorphisms.append(possibleIsomorphism)
        if areIsomorphic and returnIsomorphisms:
            return areIsomorphic, isomorphisms
        else:
            return areIsomorphic

    # Turns a single atom 'a' into a set(['a']).
    def makeset(self, x):
        if type(x) == str:
            x = set([x])
        if type(x) != type(set()):
            raise TypeError('An element of the algebra needs to be either a set of atoms or a string representing a single atom.')
        return x
    
    # Define composition of atoms or sets of atoms using the atom table.
    # We allow for inputs of single atoms, but every element is properly
    # viewed as a set of atoms.
    def compose(self, x, y):
        x = self.makeset(x)
        y = self.makeset(y)
        # Composition with the 0 element
        if x == set() or y == set():
            output = set()
        else:
            output = set()
            for i, j in itertools.product(x, y):
                rowPos = ord(i) - 97
                colPos = ord(j) - 97
                try:
                    output = output.union(self.atomTable[rowPos][colPos])
                except IndexError:
                    "Out of bounds: composition "+ str(x) + "*" + str(y) + " contains a non-atomic element."
        return output

    # Define intersection as set intersection.
    def intersection(self, x, y):
        x = self.makeset(x)
        y = self.makeset(y)
        return x.intersection(y)

    # Define union as set union.
    def union(self, x, y):
        x = self.makeset(x)
        y = self.makeset(y)
        return x.union(y)

    # Define converse using the converse dictionary we made earlier.
    def converse(self, x):
        x = self.makeset(x)
        return set([self.atomConverses[atom] for atom in x])

    # Define complement as set complement relative to the top elemenet (set of all atoms).
    def complement(self, x):
        x = self.makeset(x)
        return self.top.difference(x)

    # Return the identity of an algebra if it exists, otherwise returns None
    # If the identity element is not already recorded, will run through all elements and check for identity property.
    @property
    def identity(self):
        if self._identity == None:
            for candidateId in self.elements:
                isId = True
                for atom in self.atoms:
                    if self.compose(candidateId, atom) != atom or self.compose(atom, candidateId) != atom:
                        isId = False
                        break
                if isId:
                    self._identity = candidateId
                    break
        return self._identity

    # All non-identity atoms.
    @property
    # Return a list of atoms which are not the identity atom.
    def nonIdentityAtoms(self):
        if self._nonIdentityAtoms == None:
            if self.identity == None:
                return self.atoms
            else:
                self._nonIdentityAtoms = [x for x in self.atoms if x != self.identity]
        return self._nonIdentityAtoms

    # Determines if the algebra generated by the atom table is a nonassociative algebra.
    # Due to the construction, not all axioms need to be checked.
    # Can control the amount of reporting done on failed axioms, if any.
    def isNA(self, whatFails = False, report = False):
        if report:
            whatFails = True
        if self._isNA == None or whatFails == True:
            self._isNA = True
            failedAxioms = []
            # Axiom R01: +-commutativity: x + y = y + x
            # Axiom R02: +-associativity: x + (y + z) = (x + y) + z
            # Axiom R03: Huntington's axiom: -(-x + -y) + -(-x + y) = x
            for x,y in itertools.product(self.atoms, repeat = 2):
                firstTerm = self.complement(self.union(self.complement(x), self.complement(y)))
                secondTerm = self.complement(self.union(self.complement(x), y))
                if self.union(firstTerm, secondTerm) != x:
                    failedAxioms.append("R03")
                    break
            # Axiom R05: ;-distributivity: (x + y);z = x;z + y;z
            # Axiom R06: identity law: x;1' = x
            if self.identity == None:
                failedAxioms.append("R06")
            # Axiom R07: converse-involution: con(con(x)) = x
            #    - should not be needed if converse pairs are correctly defined.
            for x in self.atoms:
                if self.converse(self.converse(x)) != x:
                    failedAxioms.append("R07")
                    break
            # Axiom R08: converse-distributivity: con(x + y) = con(x) + con(y)
            for x,y in itertools.product(self.atoms, repeat = 2):
                if self.converse(self.union(x,y)) != self.union(self.converse(x), self.converse(y)):
                    failedAxioms.append("R09")
                    break
            # Axiom R09: converse-involutive distributivity: con(x;y) = con(y);con(x)
            for x,y in itertools.product(self.atoms, repeat = 2):
                if self.converse(self.compose(x,y)) != self.compose(self.converse(y), self.converse(x)):
                    failedAxioms.append("R09")
                    break
            # Axiom R10: Tarski/De Morgan axiom: con(x); -(x;y) + -y = y
            for x,y in itertools.product(self.atoms, repeat = 2):
                if self.union(self.compose(self.converse(x), self.complement(self.compose(x,y))), self.complement(y)) != self.complement(y):
                    failedAxioms.append("R10")
                    break
            if len(failedAxioms) > 0:
                self._isNA = False
        if report:
            self.reportFailedAxioms(failedAxioms)
            return self._isNA
        elif whatFails and not report:
            return (self._isNA, failedAxioms)
        else:
            return self._isNA

    # Determines if the algebra generated by the atom table satisfies the weakly associative axiom.
    # Axiom WA: ((id . x) . top) . top = (id . x) . (top . top)
    @property
    def satisfiesWAaxiom(self):
        if self._satisfiesWAaxiom == None:
            if self.identity == None:
                self._satisfiesWAaxiom = False
            else:
                self._satisfiesWAaxiom = True
                for x in self.atoms:
                    LHS = self.compose(self.compose(
                            self.intersection(self.identity, x), self.top), self.top)
                    RHS = self.compose(self.compose(
                            self.intersection(self.identity, x), self.top), self.compose(self.top, self.top))
                    if LHS != RHS:
                        self._satisfiesWAaxiom = False
                        break
        return self._satisfiesWAaxiom

    # Determines if the algebra generated by the atom table is a weakly associative algebra.
    # The algebra must be an nonassociative algebra and satisfy the weakly associative axiom.
    def isWA(self, whatFails = False, report = False):
        if report:
            whatFails = True
        if whatFails == True:
            self._isWA = True
            failedAxioms = []
            failedAxioms.extend(self.isNA(True,False)[1])
            if self.satisfiesWAaxiom == False:
                failedAxioms.append("WA")
            if len(failedAxioms) > 0:
                self._isWA = False
        elif self._isWA == None:
            self._isWA = (self.isNA() and self.satisfiesWAaxiom)
        if report:
            self.reportFailedAxioms(failedAxioms)
            return self._isWA
        elif whatFails and not report:
            return (self._isWA, failedAxioms)
        else:
            return self._isWA

    # Determines if the algebra generated by the atom table satisfies the semiassociative axiom.
    # Axiom SA: (x . top) . top = x . (top . top)"
    @property
    def satisfiesSAaxiom(self):
        if self._satisfiesSAaxiom == None:
            self._satisfiesSAaxiom = True
            for x in self.atoms:
                if self.compose(self.compose(x, self.top), self.top) != self.compose(self.compose(x, self.top), self.compose(self.top, self.top)):
                    self._satisfiesSAaxiom = False
                    break
        return self._satisfiesSAaxiom

    # Determines if the algebra generated by the atom table is a semiassociative algebra.
    # The algebra must be an nonassociative algebra and satisfy the semiassociative axiom.
    def isSA(self, whatFails = False, report = False):
        if report:
            whatFails = True
        if whatFails == True:
            self._isSA = True
            failedAxioms = []
            failedAxioms.extend(self.isWA(True,False)[1])
            if self.satisfiesSAaxiom == False:
                failedAxioms.append("SA")
            if len(failedAxioms) > 0:
                self._isSA = False
        elif self._isSA == None:
            self._isSA = (self.isNA() and self.satisfiesSAaxiom)
        if report:
            self.reportFailedAxioms(failedAxioms)
            return self._isSA
        elif whatFails and not report:
            return (self._isSA, failedAxioms)
        else:
            return self._isSA

    # Determines if the algebra generated by the atom table has an associative composition operation.
    # Axiom R04: ;-associativity: x;(y;z) = (x;y);z."
    @property
    def isAssociative(self):
        if self._isAssociative == None:
            self._isAssociative = True
            for i, j, k in itertools.product(self.elements, repeat = 3):
                if self.compose(self.compose(i,j), k) != self.compose(i, self.compose(j,k)):
                    self._isAssociative = False
                    break
        return self._isAssociative

    # Determines if the algebra generated by the atom table is a relation algebra.
    # Must be an associative nonassociative algebra.
    # If whatFails = True, will return a list of RA axioms that are not
    # satisfied by the algebra.
    # If report = True, a human-readable version of the failed axioms will
    # instead be returned.
    def isRA(self, whatFails = False, report = False):
        if report:
            whatFails = True
        if whatFails == True:
            self._isRA = True
            failedAxioms = []
            failedAxioms.extend(self.isSA(True,False)[1])
            if self.isAssociative == False:
                failedAxioms.append("R04")
            if len(failedAxioms) > 0:
                self._isRA = False
        elif self._isRA == None:
            self._isRA = (self.isNA() and self.isAssociative)
        if report:
            self.reportFailedAxioms(failedAxioms)
            return self._isRA
        elif whatFails and not report:
            return (self._isRA, failedAxioms)
        else:
            return self._isRA




    
    
    
    
    
    
    
    
    
    
    