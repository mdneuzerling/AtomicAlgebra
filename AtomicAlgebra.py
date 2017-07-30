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
        self.top = reduce(lambda x, y : x |y, self.atoms)
        self.zero = set()
        # The elements are the power set of the atoms.
        # It's convenient 
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
        self.symmetricAtoms = [x[0] for x in self.conversePairs if x[0] == x[1]]
        self.nonSymmetricPairs = [x for x in self.conversePairs if x[0] != x[1]]
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
    # This method seems to be powered by magic, and should be redone.
    @staticmethod
    def _stringToAtomTable(matrixString):
        M0 = matrixString.replace(" ", "")
        M1 = M0.strip()[1:-1]
        M2 = M1.strip()[1:-1]
        M3 = [line.split(',') for line in M2.split('],[')]
        M4 = [[set(entry.split("+"))-set(['0']) for entry in line] for line in M3]
        return M4  

    # Give a human readable report on a list of failed axioms, eg. ["R01", "R02", "R07"].
    @staticmethod
    def reportFailedAxioms(failedAxioms):
        if type(failedAxioms) is not list: failedAxioms = [failedAxioms]
        for axiom in failedAxioms:
            print("Fails axiom " + axiom + ": " + AtomicAlgebra.AXIOMS[axiom] + ".")
            
    # Through unions, we can extend any map between atoms to a map between
    # elements of algebras. For example, if 'a' -> 'b' and 'c' -> 'd', then  
    # {'a', 'b'} -> {'c', 'd'}. Thus, every map between atoms uniquely defines 
    # a map between elements. In practice we always define maps on atoms only.
    # We use the term "function" in reference to a map between elements.
    @staticmethod
    def atomFunction(atomMap, element):
        if type(element) is str:
            return atomMap[element]
        else:
            return set([AtomicAlgebra.atomFunction(atomMap, x) for x in element])
        
    # Check if a map between atom structures preserves composition.
    # This is a necessary, but not sufficient condition, for an atomMap or
    # atomFunction to be an isomorphism.
    def preservesComposition(self, algebra2, atomMap):
        preservesComposition = True
        for x, y in itertools.product(self.atoms, repeat = 2):
            if AtomicAlgebra.atomFunction(atomMap, self.compose(x, y)) != algebra2.compose(AtomicAlgebra.atomFunction(atomMap, x), AtomicAlgebra.atomFunction(atomMap, y)):
                preservesComposition = False
                break
        return preservesComposition

    # Checks if a given algebra is isomorphic to the instance being called from.
    # Can also return an isomorphism, if one exists.
    def isIsomorphic(self, algebra2, returnIsomorphism = False):
        # First we check that the algebras are the same size, and that the
        # number of atoms in the identity is the same.
        # These are necessary conditions for an isomorphism, so can save some time.
        if self.nAtoms != algebra2.nAtoms: return False
        if len(self.identity) != len(algebra2.identity): return False
        # Next we check that the converse pairs match in number and structure.
        # This is a necessary condition for isomorphism, so can save some time.
        if len(self.symmetricAtoms) != len(algebra2.symmetricAtoms):
            return False
        # Enumerate all possible functions respecting converse.
        # First enumerate all possible ways to map symmetric atoms from 
        # the first algebra to self converse atoms from the second algebra.
        possibleSelfConverseMaps = []
        for perm in permutations(algebra2.symmetricAtoms):
            possibleSelfConverseMaps.append(zip(self.symmetricAtoms, perm))
        possibleSelfConverseMaps = [list(p) for p in possibleSelfConverseMaps]
        # Now enumerate all possible ways to map converse pairs from the 
        # first algebra to converse pairs from the second algebra.
        possibleConversePairMaps = []
        for perm1 in list(product(*[[x,x[::-1]] for x in algebra2.nonSymmetricPairs])):
            for perm2 in permutations(perm1):
                map = []
                pairing = zip(self.nonSymmetricPairs, perm2)
                for pair in pairing:
                    map.append((pair[0][0], pair[1][0]))
                    map.append((pair[0][1], pair[1][1]))
                possibleConversePairMaps.append(map)
        # Now combine them to generate all maps respecting the converse structure.
        possibleIsomorphisms = []
        for selfConverseMap, conversePairMap in itertools.product(possibleSelfConverseMaps, possibleConversePairMaps):
            possibleIsomorphisms.append(selfConverseMap + conversePairMap)
        possibleIsomorphisms = [dict(x) for x in possibleIsomorphisms]
        # We can reduce the search space by exploiting the fact that an
        # isomorphism will always map the identity of one algebra to the identity
        # of the target algebra. We generate all possible maps from atoms in the
        # identity of the first algebra to atoms in the identity of the second
        # algebra, and then restrict the possibleIsomorphisms to those that
        # "agree" with one of the identity-preserving maps.
        algebra2IdentityPermutations = [p for p in permutations(list(algebra2.identity))]
        possibleIdentityMaps = [dict((list(self.identity)[i], y[i]) 
            for i in range(len(self.identity))) for y in algebra2IdentityPermutations]
        possibleIsomorphisms = [iso for iso in possibleIsomorphisms
            if {k: iso[k] for k in list(self.identity)} in possibleIdentityMaps]
        # Now we search through the possible isomorphisms.
        # Our final search space includes only those that respect converse and
        # identity. We now need to search through these for maps that respect
        # composition. Break if an isomorphism is found, to save time.
        areIsomorphic = False
        for possibleIsomorphism in possibleIsomorphisms:
            if self.preservesComposition(algebra2, possibleIsomorphism):
                areIsomorphic = True
                isomorphism = possibleIsomorphism
                break
        if areIsomorphic and returnIsomorphism:
            return areIsomorphic, isomorphism
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




    
    
    
    
    
    
    
    
    
    
    