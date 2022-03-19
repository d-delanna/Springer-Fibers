class LinearSystem:
    """ Provides solutions to a linear system. """
    def __init__(self, mat, vec):
        self.mat = Matrix(SR, mat)
        self.vec = vector(SR, vec)
        self.soln = self.__solve_linear_system()

    def __convert_soln_to_dict(self, soln):
        """ Changes soln from type(sage.symbolic.expressions) to type(dict). """
        var_dictionary = dict()
        for equation in soln[0]:
            try:
                equation = str(equation).split(" == ")
                var_dictionary[var(equation[0])] = int(equation[1])  # TODO: change to float
            except ValueError:
                var_dictionary[var(equation[0])] = equation[1]  # TODO: change to var
        return var_dictionary

    def __solve_linear_system(self):
        """ Given mat = A, vec = y, solve for x such that Ax = y and returns y in terms of vars of x. """
        x_vars = [var('s' + str(i)) for i in range(self.mat.ncols())]
        x = vector(SR, x_vars)
        all_vars = x_vars + list(Matrix(self.vec).variables())  # list of all vars of interest in linear system
        eqns = [(self.mat*x)[j] == self.vec[j] for j in range(self.mat.nrows())]
        soln = solve(eqns, all_vars)
        return self.__convert_soln_to_dict(soln)

class ArcDiagram:
    """ Rewrites Balanced Yamanouchi Words into an arc diagram. """
    def __init__(self, balanced_yamanouchi_word):
        self.word = balanced_yamanouchi_word
        self.letter_indices = self.__find_letter_indices()
        self.arc_diagram = self.__gen_arc_diagram()

    def __find_letter_indices(self):
        """ Returns list of list of the indices of each unique letter in word. """
        letter_indices = [[]]
        used_letters = [self.word[0]]
        for idx in range(len(self.word)):
            letter = self.word[idx]
            if letter not in used_letters:
                letter_indices += [[idx+1]]
                used_letters += [letter]
            else:
                letter_indices[used_letters.index(letter)] += [idx+1]
        return letter_indices

    def __find_unique_pairings(self, indices1, indices2):
        """ Returns list of non-crossing sub-arcs (pairings) that begin at idx1 and end at idx2. """
        pairings = []
        cp_indices2 = copy(indices2[::-1])
        for idx1 in indices1[::-1]:
            try:
                idx2 = list(map(lambda idx2 : idx2 < idx1, cp_indices2)).index(True)-1
            except ValueError:
                idx2 = -1
            pairings.insert(0, [idx1, cp_indices2[idx2]])
            del cp_indices2[idx2]
        return pairings

    def __combine_pairings(self, pairings1, pairings2):
        """ Using list of sub-arcs, returns a list of complete arcs. """
        arcs = []
        for pair1 in pairings1:
            for pair2 in pairings2:
                if pair1[-1] == pair2[0]:
                    arcs.append(pair1 + pair2[1:])
        return arcs

    def __gen_arc_diagram(self):
        """ Generates arc diagram from given word. """
        arc_diagram = self.__find_unique_pairings(self.letter_indices[0], self.letter_indices[1])
        for i in range(len(self.letter_indices)-2):
            arcs = self.__find_unique_pairings(self.letter_indices[i+1], self.letter_indices[i+2])
            arc_diagram = self.__combine_pairings(arc_diagram, arcs)
        return arc_diagram

class ArcMatrix:
    """ Produces square matrix M with entries determined by the given arc diagram.
    NOTE: M is the transpose of the matrix of mathematical interst. """
    def __init__(self, arc_diagram):
        self.arc_diagram = Matrix(arc_diagram)
        self.nrows, self.ncols = self.arc_diagram.nrows(), self.arc_diagram.ncols()
        self.dim = self.nrows * self.ncols  # dimension of M
        self.one_coords = self.__determine_one_coords()  # (i, j) locations of 1
        self.var_idx = 0  # subscript of variables
        self.M = self.__gen_arc_mat()

    def __determine_one_coords(self):
        """ Returns a list of all (i, j) entries of M that should be 1. """
        one_coords = []
        for row_idx, row in enumerate(list(self.arc_diagram.T)):
            row = list(row)
            row.sort()
            for idx, entry in enumerate(row):
                one_idx = self.nrows * (self.ncols - row_idx - 1) + idx
                one_coords += [(entry-1, one_idx)] # (row, column) of pre-transpose matrix
        return one_coords

    def __gen_first_row(self):
        """ Generates the first row of the arc matrix. """
        first_row = []
        zero_entries = [0]*(self.nrows - 1)
        for i in range(self.ncols - 1):
            first_row += [var('z'+str(i))] + zero_entries
        first_row += [1] + zero_entries
        self.var_idx += self.nrows - 1
        return first_row

    def __determine_coord_value(self, row_idx, col_idx):
        """ Assigns a 0, 1, or a variable to entries of M.
        NOTE: If an entry is below or to the right of a 1-entry, it is 0. """
        for coord_idx in range(self.dim):
            one_row, one_col = self.one_coords[coord_idx][0], self.one_coords[coord_idx][1]
            if row_idx > one_row and col_idx == one_col:  # if coordinate is to the right of a 1
                return 0
            elif row_idx == one_row and col_idx > one_col:  # if coordinate is below a 1
                return 0
            elif row_idx == one_row and col_idx == one_col:  # if coordinate should be 1
                return 1
        # if none of the above:
        self.var_idx += 1
        return var('z'+str(self.var_idx))

    def __gen_arc_mat(self):
        """ Returns the arc matrix of the arc diagram. """
        M = [self.__gen_first_row()]
        for row_idx in range(1, self.dim):
            row = [self.__determine_coord_value(row_idx, col_idx) for col_idx in range(self.dim)]
            M.append(row)
        return Matrix(M)

class RepnMatrix(ArcMatrix):
    """ Determines unkown variables of the rows of ArcMatrix.M so that
    the row is a linear combinations of the ones above it. """
    def __init__(self, arc_diagram):
        super().__init__(arc_diagram)
        self.jcf_mat = self.__make_zero_jcf_mat()
        self.__gen_repn_mat()

    def __make_zero_jcf_mat(self):
        """ Makes a Jordan Canoncial Form matrix J with 0's on the diagonal. """
        O = Matrix([[0 for _ in range(self.nrows)] for _ in range(self.nrows)])
        D = Matrix([[1 if j==(i+1) else 0 for j in range(self.nrows)] for i in range(self.nrows)])
        J = block_matrix([[D if j==i else O for j in range(self.ncols)] for i in range(self.ncols)])
        return J

    def __make_replacement_row(self, row_idx, soln):
        """ Rewriting rows of M as linear combinations of previous rows. """
        row = []
        for idx in range(self.dim):
            variable = self.M[row_idx][idx]
            try:
                if 'r' in str(soln[variable]):  # if the soln is arbitrary
                    row += [variable]  # leave as simple unknown variable
                else:  # if soln is lin comb of previous variables
                    row += [soln[variable]]  # switch out the unknown var for lin comb
            except KeyError:
                row += [variable]
        return row

    def __gen_repn_mat(self):
        """ Generates representation matrix of the arc diagram. """
        for row_idx in range(1, self.dim):
            prev_rows = Matrix([self.M.row(i) for i in range(row_idx+1)]).T  # M' := prev_cols
            challenge_row = vector(self.M.row(row_idx))  # x := challenge_row
            soln = LinearSystem(prev_rows, self.jcf_mat * challenge_row).soln  # solve lin system M' = Jx
            replacement_row = self.__make_replacement_row(row_idx, soln)
            self.M[row_idx] = replacement_row
        return self.M

    def __repr__(self):
        """ Prints M in form of mathematical interest. """
        copy_M = copy(self.M.T)
        copy_M.subdivide([int(self.nrows * i) for i in range(1, self.ncols)], None)
        return str(copy_M)
