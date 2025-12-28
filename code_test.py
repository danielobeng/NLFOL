from typing import List

def Constant(constant_name: str):
    """return a constant symbol (preserves camelCase)"""
    # Preserve camelCase: ensure first letter is uppercase, keep the rest as-is
    if constant_name:
        name = constant_name[0].lower() + constant_name[1:] if len(constant_name) > 1 else constant_name.lower()
    else:
        name = constant_name
    return name

def Variable(variable_name: str):
    # """return a variable symbol,
    # which starts with`$`"""
    # return '$' + variable_name
    return variable_name

def Function(function_name: str, terms: List[str]):
    """return a function symbol, for example,
    father(x) means the father of x"""
    return '{}({})'.format(function_name.lower(),', '.join(terms))

def Predicate(predicate_name: str, terms: List[str]):
    """return an atomic formula with a predicate,
    whose name starts with uppercase (preserves camelCase)"""
    if predicate_name:
        name = predicate_name[0].upper() + predicate_name[1:] if len(predicate_name) > 1 else predicate_name.lower()
    else:
        name = predicate_name
    return '{}({})'.format(name, ', '.join(terms))

def Equal(term_a: str, term_b: str):
    """return an atomic formula with equal operation"""
    return '{}= {}'.format(term_a, term_b)

def NonEqual(term_a: str, term_b: str):
    """return an atomic formula with equal operation"""
    return '{} \u2260 {}' .format(term_a, term_b)

def Negation(formula: str):
    """return the negation of the input formula"""
    return '\u00ac({})'.format(formula)

def Conjunction(formula_a: str, formula_b: str):
    """return the conjunction of the input formulas"""
    return '{} \u2227 {}'.format(formula_a, formula_b)

def Disjunction(formula_a: str, formula_b: str):
    """return the disjunction of the input formulas"""
    return '{} \u2228 {}'.format(formula_a, formula_b)

def Implication(antecedent_formula: str, consequent_formula: str):
    """return the implication formula of the
    antecedent formula and consequent formula"""
    return '{} \u2192 {}'.format(antecedent_formula, consequent_formula)

def Equivalence(formula_a: str, formula_b: str):
    """return the logical equivalence formula of
    the input formulas"""
    return '{} \u2194 {}'.format(formula_a, formula_b)

def Nonequivalence(formula_a: str, formula_b: str):
    """return the logical non-equivalence formula of
    the input formulas"""
    return '{} \u2295 {}'.format(formula_a, formula_b)

def ExistentialQuantification(formula: str, variable_symbol: str):
    """return an existential quantification of the input formula
    and the input variable symbol"""
    # Check if variable_symbol (with or without $) is in formula
    assert variable_symbol in formula or f'${variable_symbol}' in formula
    return '\u2203{} ({})'.format(variable_symbol, formula)

def UniversalQuantification(formula: str, variable_symbol: str):
    """return an universal quantification of the input formula
    and the input variable symbol"""
    # Check if variable_symbol (with or without $) is in formula
    assert variable_symbol in formula or f'${variable_symbol}' in formula
    return '\u2200{} ({})'.format(variable_symbol, formula)

def Parenthesize(formula: str):
    """Wrap a formula in parentheses for proper grouping"""
    return f'({formula})'

def End(formula: str):
    return formula


if __name__ == "__main__":
    formula1 = Variable('x')
    formula2 = Predicate('Film', [formula1])
    formula3 = Predicate('Drama', [formula1])
    formula4 = Predicate('LongRuntime', [formula1])
    formula5 = Conjunction(formula3, formula4)
    formula6 = Predicate('MultipleAwards', [formula1])
    formula7 = Conjunction(formula5, formula6)
    formula8 = Predicate('Comedy', [formula1])
    formula9 = Predicate('ShorterRuntime', [formula1])
    formula10 = Conjunction(formula8, formula9)
    formula11 = Predicate('BoxOfficeSuccess', [formula1])
    formula12 = Conjunction(formula10, formula11)
    formula13 = Disjunction(formula7, formula12)
    formula14 = Conjunction(formula2, formula13)
    formula15 = ExistentialQuantification(formula14, 'x')
    formula = End(formula15)


    print(formula)