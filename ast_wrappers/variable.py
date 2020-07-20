import clingo


class Variable(clingo.ast.AST):
    """
        Custom clingo AST Variable definition to correct
            errors when outputting conditional literal objects
            using their __str__ method

        NOTE: This class is unused as it is currently not needed.
    """

    def __init__(self, variable):
        self.type = variable.type
        self.child_keys = variable.child_keys
        self.location = variable.location
        self.name = variable.name

    def __str__(self):
        return self.name
