from itertools import product
from sys import platform
import multiprocessing as mp

# If the identity is atomic it will be represented by 'a'. 
# This fixes the left-most column and uppermost row of the composition table of atoms.
# A fixed entry is represented by a consistent triple, eg. ('a','a','a') or ('a','b','b').
# This function returns the cycles needed to fix an atomic identity acting on n_atoms.
def atomic_identity(n_atoms):
    atoms = [chr(i + 97) for i in range(n_atoms)]
    return [('a', atom, atom) for atom in atoms] + [(atom, 'a', atom) for atom in atoms[1:]]

# Returns the cycles fixing an identity element consists of n_atoms.
# If n_atoms == 1, cycles fixing an identity atom are returned.
# This construction assumes that the identity fragments form the first n_fragments
# atoms, ie. a three-fragment identity will be the union of a, b and c.
def fragment_identity(n_atoms, n_fragments):
    if n_fragments == 1:
        return atomic_identity(n_atoms)
    else:
        atoms = [chr(i + 97) for i in range(n_atoms)]
        return(
            [(atom, atom, atom) 
                for atom in atoms[:n_fragments]] + 
            [(atom1, atom2, 0) 
                for atom1, atom2 in product(atoms[:n_fragments], repeat=2) 
                if atom1 != atom2])
    
# Fix an entry of an atom table to either a single atom or 0.
# Input is a list of tuples of fixed entries, eg. [('a','a','b')] will fix the 
# upper-left entry to 'b' and only 'b'. Output is a list of necessary cycles, a 
# list of forbidden cycles, and a list of optional (remaining) cycles. Any 
# algebra with consistent cycles including at least those that are necessary, 
# and none of those that are forbidden, will have the desired fixed entry.
def fix_entries(entries_to_fix, cycles):
    cycles_to_sort = cycles
    necessary_cycles = []
    forbidden_cycles = []
    # a, b, c in entries_to_fix means that a;b = c is the composition we want to fix.
    for a, b, c in entries_to_fix:
        # If c == 0, then a;b composes to nothing.
        if c == 0:
            for cycle in cycles_to_sort:
                if (a,b) in [triple[:2] for triple in cycle]:
                    if cycle not in forbidden_cycles: forbidden_cycles.append(cycle)
        else:
            for cycle in cycles_to_sort:
                # If the cycle contains a;b composing to c, it is necessary.
                if (a,b,c) in cycle:
                    if cycle not in necessary_cycles: necessary_cycles.append(cycle)
                # If the cycle contains a;b composing to something other than c, it is forbidden.
                elif (a,b) in [triple[:2] for triple in cycle]:
                    if cycle not in forbidden_cycles: forbidden_cycles.append(cycle)
    # A cycle that is neither necessary or forbidden is optional.
    optional_cycles = [cycle for cycle in cycles if cycle not in necessary_cycles and cycle not in forbidden_cycles]
    return necessary_cycles, forbidden_cycles, optional_cycles

# Create an algebra from a list of cycles to be included, and a converse structure.
# First creates an atom table from the cycles, then creates an instance of the AtomicAlgebra class
def create_n_atom_algebra_from_cycles(cycles, converse, n_atoms):
    # Create an empty atom_table
    atom_table = [[set() for i in range(n_atoms)] for j in range(n_atoms)]
    # Fill the atom table.
    for cycle in cycles:
        for triple in cycle:
            x, y, z = triple
            row_pos = ord(x) - 97
            col_pos = ord(y) - 97
            # For every triple in every cycle, set the relevant entry of the atom_table to correspond to the cycle.
            atom_table[row_pos][col_pos] = atom_table[row_pos][col_pos].union(set([z]))
    new_algebra = AtomicAlgebra(atom_table, converse)
    return new_algebra

# Generate a list of nonassociative algebras with an atom_table with desired fixed entries and converse structure.
# Returned list contains no two isomorphic algebras.
# We can also specify that the identity size should be fixed, so that the number
# of atoms in the identity of the first algebra (the simples)
def generate_algebras_from_fixed_entries(entries_to_fix, converse, n_atoms, fix_identity_size = False):
    # First generate all of the cycles from the desired converse structure.
    cycles = AtomicAlgebra.cycle_partition(converse, n_atoms)
    # Then generate the necessary, forbidden and optional cycles fixing the desired entries.
    necessary_cycles, forbidden_cycles, optional_cycles = fix_entries(entries_to_fix, cycles)
    # Take the powerset of optional cycles. This is the set of choices of optional cycles to include.
    pset = [combinations(optional_cycles, n) for n in range(len(optional_cycles)+1)]
    pset = list(chain.from_iterable(pset))
    pset = [list(c) for c in pset]
    # Add the necessary cycles to every choice of optional cycles. Each possible cycle set is an algebra.
    possible_cycle_sets = [necessary_cycles + choice for choice in pset]
    algebras = []
    n_cycle_sets = len(possible_cycle_sets)
    for cycle_set in possible_cycle_sets:
        new_algebra = create_n_atom_algebra_from_cycles(cycle_set, converse, n_atoms)
        # We're only interested in nonassociative algebras
        valid_algebra = new_algebra.is_NA()
        if valid_algebra: # check for isomorphisms
            for algebra in algebras:
                if new_algebra.is_isomorphic(algebra, return_isomorphism = False):
                    valid_algebra = False
                    # If an isomorphic algebra is found, we don't need to check the rest.
                    break
        if fix_identity_size and valid_algebra: # If we want to fix the size of the identity
            if len(algebras) == 0:
                fixed_identity_size = len(new_algebra.identity)
            else:
                valid_algebra = (len(new_algebra.identity) == fixed_identity_size)
        if valid_algebra: algebras.append(new_algebra)
    return algebras

    # We may want to build in an assumption that any element not specified in 
    # the converse structure is assumed to be symmetric. To prepare for this,
    # we calculate the number of symmetric atoms based on the number of
    # non-symmetric atoms.
def generate_algebras_from_identity_and_converse(n_atoms, identity_size,
                                                 converse, verbose = False):
    n_symmetric = n_atoms - len([k for k in converse.keys() if converse[k] != k])
    creation_statement = "Generating " + str(n_atoms) + "-atom algebras with "
    if identity_size == 1: 
        creation_statement += "atomic identity "
    else:
        creation_statement += str(identity_size) + "-fragment identity "
    creation_statement += ("and " + str(n_symmetric) + " symmetric atom" + 
                          (n_symmetric != 1)*"s" + ".")
    if verbose: print(creation_statement)
    algebras = generate_algebras_from_fixed_entries(
            fragment_identity(n_atoms, identity_size), 
            converse = converse, n_atoms = n_atoms, fix_identity_size = True)
    outcome_statement = ("Found " + str(len(algebras)) + 
                             " non-isomorphic algebra" + 
                             (len(algebras) > 1) * "s" + ".")
    if verbose: print(outcome_statement)
    return algebras

def converses_respecting_identity(n_atoms, identity_size):
    converses = []
    for n_symmetric in [i for i in range(identity_size, n_atoms + 1) if (n_atoms - i) % 2 == 0]:
        n_non_symmetric = n_atoms - n_symmetric
        converse = [(chr(i + 97), chr(i + 97)) for i in range(n_symmetric)]
        for converse_pair_start in [n_symmetric + j for j in range(n_non_symmetric) if j % 2 == 0]:
            converse.append((chr(converse_pair_start + 97), chr(converse_pair_start + 97 + 1)))
        converses.append(AtomicAlgebra.converse_pairs_to_dict(converse))
    return converses

def generate_algebras(n_atoms):
    algebras = []
    for identity_size in range(1, n_atoms + 1):
        for converse in converses_respecting_identity(n_atoms, identity_size):
            algebras += generate_algebras_from_identity_and_converse(
                    n_atoms, identity_size, converse, verbose = True
                    )
    return(algebras)
