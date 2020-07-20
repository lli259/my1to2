"""Constants File"""

NON_AGGR_FORM = 0  # Form:  F(X1), ..., F(Xb), X1 != Xb, X1 != Xi, ..., Xi != Xb
AGGR_FORM1 = 1  # Form:  b <= #count{ X : f(X) }
AGGR_FORM2 = 2  # Form:  not #count{ Y : f(Y) } < b
AGGR_FORM3 = 3  # Form:  not b - 1 = #count{ Y : f(Y) }, ..., not 0 = #count{ Y : f(Y) }

FORM_TRANSLATION = {
    NON_AGGR_FORM: "Non-aggregate",
    AGGR_FORM1: "Inequality Aggregate",
    AGGR_FORM2: "Negated Inequality Aggregate",
    AGGR_FORM3: "Negated Equality Aggregate"
}

# Useful for pretty printing in print_valid_output_forms method
FORM_TRANSLATION_PADDING = {
    NON_AGGR_FORM: "               ",
    AGGR_FORM1: "        ",
    AGGR_FORM2: "",
    AGGR_FORM3: "  "
}

LOCATION = {    # Custom 'Location' value for aagg-created AST objects, which do not correspond to a real file location
    'begin': {'column': 'inserted-by-aagg', 'line': 'inserted-by-aagg', 'filename': '<string>'},
    'end': {'column': 'inserted-by-aagg', 'line': 'inserted-by-aagg', 'filename': '<string>'}
}
