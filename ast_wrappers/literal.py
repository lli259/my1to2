import clingo


class Literal(clingo.ast.AST):
    """
        Custom clingo AST AggregateLiteral definition to correct
            errors when outputting conditional literal objects
            using their __str__ method

        NOTE: This class is unused as it is currently not needed.
    """

    def __init__(self, literal):
        self.type = literal.type
        self.child_keys = literal.child_keys
        self.location = literal.location
        self.sign = literal.sign
        self.atom = literal.atom

    def __str__(self):
        return "%s %s" % self.sign, self.atom
