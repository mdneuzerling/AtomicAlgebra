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
    def __init__(self, atom_table, converse = None):
        if type(atom_table) == str:
            atom_table = self._string_to_atom_table(atom_table)
        self.n_atoms = len(atom_table[0])
        self.atoms = [set([chr(i + 97)]) for i in range(self.n_atoms)]
        self.atom_table = atom_table
        # If no converses given assume all atoms are symmetric.
        if converse == None: 
            self.converse = [(x,x) for x in [chr(i + 97) for i in range(self.n_atoms)]]
        # Can give atoms as a dictionary on atoms...
        if type(converse) is dict:
            self.converse_pairs = self.converse_dict_to_pairs(converse)
            self.converse_dict = converse
        # ... or as a list of tuples.
        else:
            self.converse_pairs = converse
            self.converse_dict = self.converse_pairs_to_dict(converse)
        # set up the basic properties of the algebra.
        self._non_identity_atoms = None
        self.top = reduce(lambda x, y : x | y, self.atoms)
        self.zero = set()
        # The elements are the power set of the atoms.
        self.elements = [combinations(list(self.top), n) for n in range(self.n_atoms + 1)]
        self.elements = list(chain.from_iterable(self.elements))
        self.elements = [set(element) for element in self.elements]
        self.n_elements = 2**self.n_atoms 
        self.n_non_zero_elements = self.n_elements - 1
        self.symmetric_atoms = [x[0] for x in self.converse_pairs if x[0] == x[1]]
        self.non_symmetric_pairs = [x for x in self.converse_pairs if x[0] != x[1]]
        self._cyclePartition = self.cycle_partition(self.converse_dict, self.n_atoms)
        self._identity = None
        self._semigroup = None
        # properties
        self._is_NA = None
        self._satisfies_WA_axiom = None
        self._is_WA = None
        self._satisfies_SA_axiom = None
        self._is_SA = None
        self._is_associative = None
        self._is_RA = None

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
    def _string_to_atom_table(matrix_string):
        M0 = matrix_string.replace(" ", "")
        M1 = M0.strip()[1:-1]
        M2 = M1.strip()[1:-1]
        M3 = [line.split(',') for line in M2.split('],[')]
        M4 = [[set(entry.split("+"))-set(['0']) for entry in line] for line in M3]
        return M4  

    # Converses can be given as a list of tuples [('a', 'a'), ('b', 'c')] or a
    # dictionary on atoms {'a': 'a', 'b': 'c', 'c': 'b'}. Tne following 
    # methods convert between the two.
    @staticmethod
    def converse_pairs_to_dict(converse_pairs):
        converse_dict = dict()
        for converse_pair in converse_pairs:
            if converse_pair[0] == converse_pair[1]: # symmetric atom
                converse_dict[converse_pair[0]] = converse_pair[0]
            else: # non-symmetric atoms
                converse_dict[converse_pair[0]] = converse_pair[1]
                converse_dict[converse_pair[1]] = converse_pair[0]
        return converse_dict

    @staticmethod
    def converse_dict_to_pairs(converse_dict):
        converse_pairs = []
        for pair in converse_dict.items():
            if pair not in converse_pairs and pair[::-1] not in converse_pairs:
                converse_pairs.append(pair)
        return converse_pairs
    
    # Given a triple and a converse structure, generate the cycle including that triple.
    # This is an implementation of the relation algebra concept of a Peircean transform.
    # Cycle generated by (x,y,z) is:
        # [ (x,y,z), (con(x),z,y), (y,con(z),con(x)),
        #   (con(y),con(x),con(z)),(con(z),x,con(y)), (z,con(y),x) ]
    # A triple in a cycle is consistent if and only if all triples in the cycle are consistent.
    @staticmethod
    def cycle(triple, converse_dict):
        if type(converse_dict) is not dict:
            converse_dict = AtomicAlgebra.converse_pairs_to_dict(converse_dict)
        x, y, z = triple
        cycle = []
        cycle.append(triple)
        cycle.append((converse_dict[x], z, y))
        cycle.append((y, converse_dict[z], converse_dict[x]))
        cycle.append((converse_dict[y], converse_dict[x], converse_dict[z]))
        cycle.append((converse_dict[z], x, converse_dict[y]))
        cycle.append((z, converse_dict[y], x))
        cycle.sort() # Prevents duplicates when using cycle_partition
        return list(set(cycle)) # Remove duplicates.

    # Given a converse structure, partition the triples of elements into cycles.
    @staticmethod
    def cycle_partition(converse_dict, n_atoms):
        if type(converse_dict) is not dict:
            converse_dict = AtomicAlgebra.converse_pairs_to_dict(converse_dict)
        atoms = [chr(i + 97) for i in range(n_atoms)]
        parts = []
        for triple in product(atoms, repeat = 3):
            cycle = AtomicAlgebra.cycle(triple, converse_dict)
            if cycle not in parts: parts.append(cycle)
        return parts

    # Give a human readable report on a list of failed axioms, eg. ["R01", "R02", "R07"].
    @staticmethod
    def report_failed_axioms(failed_axioms):
        if type(failed_axioms) is not list: failed_axioms = [failed_axioms]
        for axiom in failed_axioms:
            print("Fails axiom " + axiom + ": " + AtomicAlgebra.AXIOMS[axiom] + ".")
            
    # Through unions, we can extend any map between atoms to a map between
    # elements of algebras. For example, if 'a' -> 'b' and 'c' -> 'd', then  
    # {'a', 'b'} -> {'c', 'd'}. Thus, every map between atoms uniquely defines 
    # a map between elements. In practice we always define maps on atoms only.
    # We use the term "function" in reference to a map between elements.
    @staticmethod
    def atom_function(atom_map, element):
        if type(element) is str:
            return atom_map[element]
        else:
            return set([AtomicAlgebra.atom_function(atom_map, x) for x in element])

    # Turns a single atom 'a' into a set(['a']).
    @staticmethod
    def make_set(x):
        if type(x) == str:
            x = set([x])
        if type(x) != type(set()):
            raise TypeError('An element of the algebra needs to be either a set of atoms or a string representing a single atom.')
        return x

    # Check if a map between atom structures preserves composition.
    # This is a necessary, but not sufficient condition, for an atom_map or
    # atom_function to be an isomorphism.
    def preserves_composition(self, other, atom_map):
        preserves_composition = True
        for x, y in product(self.atoms, repeat = 2):
            if AtomicAlgebra.atom_function(atom_map, self.compose(x, y)) != other.compose(AtomicAlgebra.atom_function(atom_map, x), AtomicAlgebra.atom_function(atom_map, y)):
                preserves_composition = False
                break
        return preserves_composition

    # Checks if a given algebra is isomorphic to the instance being called from.
    # Can also return an isomorphism, if one exists.
    def is_isomorphic(self, other, return_isomorphism = False):
        # First we check that the algebras are the same size, and that the
        # number of atoms in the identity is the same.
        # These are necessary conditions for an isomorphism, so can save some time.
        if self.n_atoms != other.n_atoms: return False
        if len(self.identity) != len(other.identity): return False
        # Next we check that the converse pairs match in number and structure.
        # This is a necessary condition for isomorphism, so can save some time.
        if len(self.symmetric_atoms) != len(other.symmetric_atoms):
            return False
        # Enumerate all possible functions respecting converse.
        # First enumerate all possible ways to map symmetric atoms from 
        # the first algebra to self converse atoms from the second algebra.
        possible_symmetric_maps = []
        for perm in permutations(other.symmetric_atoms):
            possible_symmetric_maps.append(zip(self.symmetric_atoms, perm))
        possible_symmetric_maps = [list(p) for p in possible_symmetric_maps]
        # Now enumerate all possible ways to map converse pairs from the 
        # first algebra to converse pairs from the second algebra.
        possible_converse_pair_maps = []
        for perm1 in list(product(*[[x,x[::-1]] for x in other.non_symmetric_pairs])):
            for perm2 in permutations(perm1):
                map = []
                pairing = zip(self.non_symmetric_pairs, perm2)
                for pair in pairing:
                    map.append((pair[0][0], pair[1][0]))
                    map.append((pair[0][1], pair[1][1]))
                possible_converse_pair_maps.append(map)
        # Now combine them to generate all maps respecting the converse structure.
        possible_isomorphisms = []
        for symmetric_map, converse_pair_map in product(possible_symmetric_maps, possible_converse_pair_maps):
            possible_isomorphisms.append(symmetric_map + converse_pair_map)
        possible_isomorphisms = [dict(x) for x in possible_isomorphisms]
        # We can reduce the search space by exploiting the fact that an
        # isomorphism will always map the identity of one algebra to the identity
        # of the target algebra. We generate all possible maps from atoms in the
        # identity of the first algebra to atoms in the identity of the second
        # algebra, and then restrict the possible_isomorphisms to those that
        # "agree" with one of the identity-preserving maps.
        other_identity_permutations = [p for p in permutations(list(other.identity))]
        possible_identity_maps = [dict((list(self.identity)[i], y[i]) 
            for i in range(len(self.identity))) 
            for y in other_identity_permutations]
        possible_isomorphisms = [iso for iso in possible_isomorphisms
            if {k: iso[k] for k in list(self.identity)} in possible_identity_maps]
        # Now we search through the possible isomorphisms.
        # Our final search space includes only those that respect converse and
        # identity. We now need to search through these for maps that respect
        # composition. Break if an isomorphism is found, to save time.
        is_isomorphic = False
        for possible_isomorphism in possible_isomorphisms:
            if self.preserves_composition(other, possible_isomorphism):
                is_isomorphic = True
                isomorphism = possible_isomorphism
                break
        if is_isomorphic and return_isomorphism:
            return is_isomorphic, isomorphism
        else:
            return is_isomorphic
    
    # Define composition of atoms or sets of atoms using the atom table.
    # We allow for inputs of single atoms, but every element is properly
    # viewed as a set of atoms.
    def compose(self, x, y):
        x = self.make_set(x)
        y = self.make_set(y)
        # Composition with the 0 element
        if x == set() or y == set():
            output = set()
        else:
            output = set()
            for i, j in product(x, y):
                row_pos = ord(i) - 97
                col_pos = ord(j) - 97
                try:
                    output = output.union(self.atom_table[row_pos][col_pos])
                except IndexError:
                    "Out of bounds: composition "+ str(x) + "*" + str(y) + " contains a non-atomic element."
        return output

    # Define intersection as set intersection.
    def intersection(self, x, y):
        x = self.make_set(x)
        y = self.make_set(y)
        return x.intersection(y)

    # Define union as set union.
    def union(self, x, y):
        x = self.make_set(x)
        y = self.make_set(y)
        return x.union(y)

    # Define converse using the converse dictionary we made earlier.
    def converse(self, x):
        x = self.make_set(x)
        return set([self.converse_dict[atom] for atom in x])

    # Define complement as set complement relative to the top elemenet (set of all atoms).
    def complement(self, x):
        x = self.make_set(x)
        return self.top.difference(x)

    # Return the identity of an algebra if it exists, otherwise returns None
    # If the identity element is not already recorded, will run through all 
    # elements and check for identity property.
    @property
    def identity(self):
        if self._identity == None:
            for candidate_identity in self.elements:
                isId = True
                for atom in self.atoms:
                    if self.compose(candidate_identity, atom) != atom or self.compose(atom, candidate_identity) != atom:
                        isId = False
                        break
                if isId:
                    self._identity = candidate_identity
                    break
        return self._identity

    # All non-identity atoms.
    @property
    # Return a list of atoms which are not the identity atom.
    def non_identity_atoms(self):
        if self._non_identity_atoms == None:
            if self.identity == None:
                return self.atoms
            else:
                self._non_identity_atoms = [x for x in self.atoms if x != self.identity]
        return self._non_identity_atoms

    # Determines if the algebra generated by the atom table is a nonassociative algebra.
    # Due to the construction, not all axioms need to be checked.
    # Can control the amount of reporting done on failed axioms, if any.
    def is_NA(self, what_fails = False, report = False):
        if report:
            what_fails = True
        if self._is_NA == None or what_fails == True:
            self._is_NA = True
            failed_axioms = []
            # Axiom R01: +-commutativity: x + y = y + x
            # Axiom R02: +-associativity: x + (y + z) = (x + y) + z
            # Axiom R03: Huntington's axiom: -(-x + -y) + -(-x + y) = x
            for x,y in product(self.atoms, repeat = 2):
                first_term = self.complement(self.union(self.complement(x), self.complement(y)))
                second_term = self.complement(self.union(self.complement(x), y))
                if self.union(first_term, second_term) != x:
                    failed_axioms.append("R03")
                    break
            # Axiom R05: ;-distributivity: (x + y);z = x;z + y;z
            # Axiom R06: identity law: x;1' = x
            if self.identity == None:
                failed_axioms.append("R06")
            # Axiom R07: converse-involution: con(con(x)) = x
            #    - should not be needed if converse pairs are correctly defined.
            for x in self.atoms:
                if self.converse(self.converse(x)) != x:
                    failed_axioms.append("R07")
                    break
            # Axiom R08: converse-distributivity: con(x + y) = con(x) + con(y)
            for x,y in product(self.atoms, repeat = 2):
                if self.converse(self.union(x,y)) != self.union(self.converse(x), self.converse(y)):
                    failed_axioms.append("R09")
                    break
            # Axiom R09: converse-involutive distributivity: con(x;y) = con(y);con(x)
            for x,y in product(self.atoms, repeat = 2):
                if self.converse(self.compose(x,y)) != self.compose(self.converse(y), self.converse(x)):
                    failed_axioms.append("R09")
                    break
            # Axiom R10: Tarski/De Morgan axiom: con(x); -(x;y) + -y = y
            for x,y in product(self.atoms, repeat = 2):
                if self.union(self.compose(self.converse(x), self.complement(self.compose(x,y))), self.complement(y)) != self.complement(y):
                    failed_axioms.append("R10")
                    break
            if len(failed_axioms) > 0:
                self._is_NA = False
        if report:
            self.report_failed_axioms(failed_axioms)
            return self._is_NA
        elif what_fails and not report:
            return (self._is_NA, failed_axioms)
        else:
            return self._is_NA

    # Determines if the algebra generated by the atom table satisfies the weakly associative axiom.
    # Axiom WA: ((id . x) . top) . top = (id . x) . (top . top)
    @property
    def satisfies_WA_axiom(self):
        if self._satisfies_WA_axiom == None:
            if self.identity == None:
                self._satisfies_WA_axiom = False
            else:
                self._satisfies_WA_axiom = True
                for x in self.atoms:
                    LHS = self.compose(self.compose(
                            self.intersection(self.identity, x), self.top), self.top)
                    RHS = self.compose(self.compose(
                            self.intersection(self.identity, x), self.top), self.compose(self.top, self.top))
                    if LHS != RHS:
                        self._satisfies_WA_axiom = False
                        break
        return self._satisfies_WA_axiom

    # Determines if the algebra generated by the atom table is a weakly associative algebra.
    # The algebra must be an nonassociative algebra and satisfy the weakly associative axiom.
    def is_WA(self, what_fails = False, report = False):
        if report:
            what_fails = True
        if what_fails == True:
            self._is_WA = True
            failed_axioms = []
            failed_axioms.extend(self.is_NA(True,False)[1])
            if self.satisfies_WA_axiom == False:
                failed_axioms.append("WA")
            if len(failed_axioms) > 0:
                self._is_WA = False
        elif self._is_WA == None:
            self._is_WA = (self.is_NA() and self.satisfies_WA_axiom)
        if report:
            self.report_failed_axioms(failed_axioms)
            return self._is_WA
        elif what_fails and not report:
            return (self._is_WA, failed_axioms)
        else:
            return self._is_WA

    # Determines if the algebra generated by the atom table satisfies the semiassociative axiom.
    # Axiom SA: (x . top) . top = x . (top . top)"
    @property
    def satisfies_SA_axiom(self):
        if self._satisfies_SA_axiom == None:
            self._satisfies_SA_axiom = True
            for x in self.atoms:
                if self.compose(self.compose(x, self.top), self.top) != self.compose(self.compose(x, self.top), self.compose(self.top, self.top)):
                    self._satisfies_SA_axiom = False
                    break
        return self._satisfies_SA_axiom

    # Determines if the algebra generated by the atom table is a semiassociative algebra.
    # The algebra must be an nonassociative algebra and satisfy the semiassociative axiom.
    def is_SA(self, what_fails = False, report = False):
        if report:
            what_fails = True
        if what_fails == True:
            self._is_SA = True
            failed_axioms = []
            failed_axioms.extend(self.is_WA(True,False)[1])
            if self.satisfies_SA_axiom == False:
                failed_axioms.append("SA")
            if len(failed_axioms) > 0:
                self._is_SA = False
        elif self._is_SA == None:
            self._is_SA = (self.is_NA() and self.satisfies_SA_axiom)
        if report:
            self.report_failed_axioms(failed_axioms)
            return self._is_SA
        elif what_fails and not report:
            return (self._is_SA, failed_axioms)
        else:
            return self._is_SA

    # Determines if the algebra generated by the atom table has an associative composition operation.
    # Axiom R04: ;-associativity: x;(y;z) = (x;y);z."
    @property
    def is_associative(self):
        if self._is_associative == None:
            self._is_associative = True
            for i, j, k in product(self.elements, repeat = 3):
                if self.compose(self.compose(i,j), k) != self.compose(i, self.compose(j,k)):
                    self._is_associative = False
                    break
        return self._is_associative

    # Determines if the algebra generated by the atom table is a relation algebra.
    # Must be an associative nonassociative algebra.
    # If what_fails = True, will return a list of RA axioms that are not
    # satisfied by the algebra.
    # If report = True, a human-readable version of the failed axioms will
    # instead be returned.
    def is_RA(self, what_fails = False, report = False):
        if report:
            what_fails = True
        if what_fails == True:
            self._is_RA = True
            failed_axioms = []
            failed_axioms.extend(self.is_SA(True, False)[1])
            if self.is_associative == False:
                failed_axioms.append("R04")
            if len(failed_axioms) > 0:
                self._is_RA = False
        elif self._is_RA == None:
            self._is_RA = (self.is_NA() and self.is_associative)
        if report:
            self.report_failed_axioms(failed_axioms)
            return self._is_RA
        elif what_fails and not report:
            return (self._is_RA, failed_axioms)
        else:
            return self._is_RA




    
    
    
    
    
    
    
    
    
    
    