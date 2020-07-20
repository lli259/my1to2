import clingo
import constants
from ast_wrappers.variable import Variable


def merge_dictionaries(dictionary1, dictionary2):
    """
        Currently accepted beth method of merging dictonaries in python2
    """
    new_dictionary = dictionary1.copy()
    new_dictionary.update(dictionary2)
    return new_dictionary

def standardize_aggregate_literal(aggregate_literal):
    """
        Processes an aggregate literal and returns in a more standard
         format for the input/output form identifiers
        Pre-check must first be verified.
        Given an aggregate with a single left guard or both guards of equality
         for the same term symbol.
        Removes the right guard in the second case.
        Standardizes left guards s.t.
            '<' becomes '<=' with an integer increment
            '>=' becomes '>' with an integer decrement
        Returns standardized aggregate literal

        TODO: Error handling for conversion of symbol to int when
                symbol is alphabetic instead of numeric.
            Note that comparing an alphabetic value is logic nonsense,
                but is syntactically valid
            Would want to put a check in the pre_check_rewritability
                function
    """
    aggregate_literal['atom']['right_guard'] = None

    if aggregate_literal['atom']['left_guard']['comparison'] == clingo.ast.ComparisonOperator.LessThan:
        # Rewrite the comparison '<' to '<=' and increment the guard value
        aggregate_literal['atom']['left_guard']['comparison'] = clingo.ast.ComparisonOperator.LessEqual
        guard_value = int(str(aggregate_literal['atom']['left_guard']['term']['symbol']))
        aggregate_literal['atom']['left_guard']['term']['symbol'] = \
            clingo.ast.Symbol(constants.LOCATION, guard_value + 1)

    elif aggregate_literal['atom']['left_guard']['comparison'] == clingo.ast.ComparisonOperator.GreaterEqual:
        # Rewrite the comparison '<' to '<=' and increment the guard value
        aggregate_literal['atom']['left_guard']['comparison'] = clingo.ast.ComparisonOperator.GreaterThan
        guard_value = int(str(aggregate_literal['atom']['left_guard']['term']['symbol']))
        aggregate_literal['atom']['left_guard']['term']['symbol'] = \
            clingo.ast.Symbol(constants.LOCATION, guard_value + 1)

    return aggregate_literal


def pre_check_rewritability(aggregate_literal):
    """
        Pre-checks rewritability by seeing whether both aggregate guards
         are not None.
        We only rewrite counting aggregates with one guard filled and one
         guard empty (unless both guards are equality for the same value;
        which is uncommonly seen but possible)
        When only one guard is present, the parse automatically rewrites
         right guards into left guards and changes the comparison operator
         accordingly.
        The pre-check checks whether there is only one (left) guard or if
         both guards are present and the comparisons are equality for the
         same value. This helps for standardizing the literal before the
         full rewritability check.
        Returns True if pre-check passes, false otherwise

        TODO: Add a check that aggregate guard term symbols are integers. This
                is needed here and for the aggregate data getter method
        TODO: Acceptance and handling of similar equivalent forms. Ex:
                b < #count{}   <==>   b+1 <= #count{}
    """
    if aggregate_literal['atom']['function'] != clingo.ast.AggregateFunction.Count:
        # not counting aggregate
        return False

    elif aggregate_literal['atom']['left_guard'] is None:
        # no guards
        return False
    elif aggregate_literal['atom']['right_guard'] is None:
        if aggregate_literal['atom']['left_guard']['term'].type == clingo.ast.ASTType.Symbol:
            # left guard exists and right guard does not (one guard total)
            # and left guard term is a symbol
            return True
        else:
            # left guard exists, right guard does not, but left guard is not
            # of a symbol
            return False
    elif aggregate_literal['atom']['left_guard']['comparison'] == clingo.ast.ComparisonOperator.Equal and \
        aggregate_literal['atom']['right_guard']['comparison'] == clingo.ast.ComparisonOperator.Equal and \
        aggregate_literal['atom']['left_guard']['term'].type == clingo.ast.ASTType.Symbol and \
        aggregate_literal['atom']['right_guard']['term'].type == clingo.ast.ASTType.Symbol and \
        str(aggregate_literal['atom']['left_guard']['term']['symbol']) == str(aggregate_literal['atom']['right_guard']['term']['symbol']):
        # we know both guards exist because of the previous conditions
        # both guards are equality comparisons of the same value
        # and both guards terms are a matching symbol
        return True

    return False  # false otherwise


def get_non_nested_variables(variable_list):
    """
        Given a variable list (tuple or list of arguments or otherwise)
        Returns an array of the non-nested variables in the variable list
    """
    non_nested_variables = []
    for term in variable_list:
        if term.type == clingo.ast.ASTType.Variable:
            non_nested_variables.append(term)
    return non_nested_variables


class AggregateCounter:
    """This class is used to track the aggregate literals within a rule"""

    def __init__(self):
        self.rewritable_aggregate_data = {
            constants.AGGR_FORM1: [],
            constants.AGGR_FORM2: [],
            constants.AGGR_FORM3: []
        }
        # Format:  { aggregate_form_id :
        #              ( variable , function, guard value, aggregate literal ) }

    def get_rewritable_variable_and_function(self, aggregate_literal):
        """
            Given a standardized aggregate literal. Only left guards are present
            Verifies rewritability of aggregates by ensuring:
                Literal sign and Aggregate guards match one of:
                    (1)  Positive and Left (<=)
                    (2)  Negative and Left (>)
                    (3)  Negative and Left (=)
                Aggregate literal contains only one aggregate element.
                There is only one aggregate element literal.
                Aggregate element literal contains a single function.
                Aggregate element tuple contains a variable used in the
                 aggregate element literal.

            Returns the (first encountered; non-nested) variable in both the
             aggregate literal element tuple and aggregate element literal atom
             function as a one-element dictionary in the following form:
                    { aggregate_form_id : ( variable , function, guard_value ) }
            Returns an empty dictionary if the literal is not rewritable
        """
        literal_type = None
        if aggregate_literal['sign'] == clingo.ast.Sign.NoSign and \
                aggregate_literal['atom']['left_guard']['comparison'] == clingo.ast.ComparisonOperator.LessEqual:
            literal_type = constants.AGGR_FORM1
        elif aggregate_literal['sign'] == clingo.ast.Sign.Negation and \
                 aggregate_literal['atom']['left_guard']['comparison'] == clingo.ast.ComparisonOperator.GreaterThan:
            literal_type = constants.AGGR_FORM2
        elif aggregate_literal['sign'] == clingo.ast.Sign.Negation and \
                 aggregate_literal['atom']['left_guard']['comparison'] == clingo.ast.ComparisonOperator.Equal:
            literal_type = constants.AGGR_FORM3
        if literal_type is None:
            return {}

        if len(aggregate_literal['atom']['elements']) != 1 or \
            len(aggregate_literal['atom']['elements'][0]['condition']) != 1 or \
            aggregate_literal['atom']['elements'][0]['condition'][0]['sign'] != clingo.ast.Sign.NoSign or \
            aggregate_literal['atom']['elements'][0]['condition'][0]['atom'].type != clingo.ast.ASTType.SymbolicAtom or \
            aggregate_literal['atom']['elements'][0]['condition'][0]['atom']['term'].type != clingo.ast.ASTType.Function:
            # aggregate literal does not contain only one aggregate element or
            # aggregate element literal does not contain only one condition or
            # aggregate element literal condition literal is not positive or
            # aggregate element literal condition literal is not a symbolic atom
            # aggregate element literal condition literal atom term is not a
            #  function
            return {}

        tuple_variables = get_non_nested_variables(aggregate_literal['atom']['elements'][0]['tuple'])
        literal_variables = get_non_nested_variables(aggregate_literal['atom']['elements'][0]['condition'][0]['atom']['term']['arguments'])
        tuple_variable_in_literal_args = None
        literal_variables_strings = [str(literal_variable) for literal_variable in literal_variables]
        for tuple_variable in tuple_variables:
            # TODO: better identification of a counting variable here.
            #       For example, two variables may be candidate per the
            #        stipulations below, but only one may allow the rule as a
            #        whole to be rewritable due to other counting variable
            #        stipulations
            if str(tuple_variable) in literal_variables_strings:
                tuple_variable_in_literal_args = tuple_variable
        if tuple_variable_in_literal_args is None:
            # aggregate element tuple does not contain a non-nested variable
            #  used in the aggregate element literal or
            # tuple does not contain the conditional literal atom term function
            #  (non-nested)
            # the variable must be non-nested s.t. it does not occur in a
            #  different function
            return {}

        guard_value = int(str(aggregate_literal['atom']['left_guard']['term']['symbol']))
        rewritable_function = aggregate_literal['atom']['elements'][0]['condition'][0]['atom']['term']
        return {literal_type: (tuple_variable_in_literal_args,
                               rewritable_function,
                               guard_value,
                               aggregate_literal)}

    def record_aggregate_literal(self, aggregate_literal):
        """
            Records rewritable aggregate literals in a standard format
        """
        if not pre_check_rewritability(aggregate_literal):
            return

        standardized_aggregate_literal = standardize_aggregate_literal(
            aggregate_literal)

        rewritable_data = self.get_rewritable_variable_and_function(standardized_aggregate_literal)
        if len(rewritable_data.keys()) != 0:
            for aggregate_id in rewritable_data:
                self.rewritable_aggregate_data[aggregate_id].append(rewritable_data[aggregate_id])
