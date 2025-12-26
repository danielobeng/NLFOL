from __future__ import annotations
from pyleri import Grammar, Keyword, Regex, Sequence, Choice, Ref, List, Repeat, Optional
from dataclasses import dataclass, field
from typing import List as TypingList, Optional as TypingOptional, Set, Dict, Tuple
from pprint import pprint

# -------------------------
# 1) Grammar (yours)
# -------------------------
class FOL(Grammar):
    r_name = Regex(r"[A-Za-z_][A-Za-z0-9_]*")

    k_forall = Choice(Keyword("forall"), "∀")
    k_exists = Choice(Keyword("exists"), "∃")
    k_not = Choice(Keyword("not"), "¬")
    k_and = Choice(Keyword("and"), "∧")
    k_or = Choice(Keyword("or"), "∨")

    TERM = Ref()
    FORMULA = Ref()

    func_term = Sequence(r_name, "(", List(TERM, delimiter=",", mi=1), ")")
    TERM = Choice(func_term, r_name)

    pred_atom = Sequence(r_name, "(", List(TERM, delimiter=",", mi=1), ")")
    eq_atom = Sequence(TERM, "=", TERM)
    ATOM = Choice(eq_atom, pred_atom)

    QUANT = Sequence(Choice(k_forall, k_exists), List(r_name, delimiter=",", mi=1), Optional("."), FORMULA)

    BASE = Choice(QUANT, ATOM, Sequence("(", FORMULA, ")"))

    NOT = Choice(Sequence(k_not, BASE), BASE)
    AND = Sequence(NOT, Repeat(Sequence(k_and, NOT)))
    OR  = Sequence(AND, Repeat(Sequence(k_or, AND)))

    IMPL = Ref()
    IMPL = Sequence(OR, Optional(Sequence(Choice("->", "→"), IMPL)))

    FORMULA = Sequence(IMPL, Optional(Sequence(Choice("<->", "↔"), IMPL)))

    START = Repeat(FORMULA, 1, 1)


# -------------------------
# 2) Clean tree node (like paper)
# -------------------------
@dataclass
class FOLGrammarTreeNode:
    start: int
    end: int
    string: str
    type: str
    value: TypingOptional[str] = None
    children: TypingList["FOLGrammarTreeNode"] = field(default_factory=list)


# -------------------------
# 3) Pyleri -> FOLGrammarTreeNode (your function, unchanged)
# -------------------------
WRAP_NAMES = {"START", "FORMULA", "BASE"}
WRAP_ELEMS = {"Ref", "Choice"}

def _ename(n) -> TypingOptional[str]:
    return getattr(getattr(n, "element", None), "name", None)

def _ecls(n) -> str:
    return getattr(getattr(n, "element", None), "__class__", type("X", (), {})).__name__

def _kids(n) -> TypingList:
    return getattr(n, "children", []) or []

def _is_tok(n, s: str) -> bool:
    return _ecls(n) == "Token" and getattr(n, "string", None) == s

def _find_named(n, target: str):
    if _ename(n) == target:
        return n
    for c in _kids(n):
        r = _find_named(c, target)
        if r is not None:
            return r
    return None

def _unwrap(n):
    cur = n
    while True:
        k = _kids(cur)
        if _ecls(cur) == "Sequence" and len(k) == 3 and _is_tok(k[0], "(") and _is_tok(k[2], ")"):
            cur = k[1]
            continue

        k = _kids(cur)
        if len(k) == 1 and (_ename(cur) in WRAP_NAMES or _ecls(cur) in WRAP_ELEMS):
            cur = k[0]
            continue

        if len(k) == 1 and _ename(cur) in {"IMPL", "OR", "AND"}:
            cur = k[0]
            continue

        return cur

def _list_children_of_name(list_node, child_rule_name: str):
    return [c for c in _kids(list_node) if _ename(c) == child_rule_name]

def pyleri_to_FOLGrammarTreeNode(py_node, bound_vars: TypingOptional[Set[str]] = None) -> FOLGrammarTreeNode:
    bound_vars = set() if bound_vars is None else set(bound_vars)
    n = _unwrap(py_node)
    rule = _ename(n)

    def mk(node, typ: str, value: TypingOptional[str] = None) -> FOLGrammarTreeNode:
        return FOLGrammarTreeNode(node.start, node.end, node.string, typ, value=value)

    def term(node, bound: Set[str]) -> FOLGrammarTreeNode:
        node = _unwrap(node)
        r = _ename(node)

        if r == "TERM" and _kids(node):
            return term(_kids(node)[0], bound)

        if r == "r_name" and _ecls(node) == "Regex":
            ident = node.string
            return mk(node, "variable" if ident in bound else "constant", value=ident)

        if r == "func_term" or (_ecls(node) == "Sequence" and _kids(node) and _ename(_kids(node)[0]) == "r_name"):
            k = _kids(node)
            fname = k[0].string
            list_node = next((c for c in k if _ecls(c) == "List"), None)
            if list_node is None:
                raise ValueError("func_term missing List(...)")
            args = [term(tn, bound) for tn in _list_children_of_name(list_node, "TERM")]
            out = mk(node, "function", value=fname)
            out.children.extend(args)
            return out

        raise ValueError(f"Unhandled TERM node: name={r}, class={_ecls(node)}, string={getattr(node,'string',None)!r}")

    if rule == "QUANT":
        k = _kids(n)
        kw = _find_named(k[0], "k_forall") or _find_named(k[0], "k_exists")
        if kw is None:
            raise ValueError("QUANT missing forall/exists keyword")
        qtype = "forall" if _ename(kw) == "k_forall" else "exists"

        var_list = k[1]
        vars_ = [c.string for c in _list_children_of_name(var_list, "r_name")]

        out = mk(n, qtype)
        for v in vars_:
            out.children.append(FOLGrammarTreeNode(-1, -1, v, "variable", value=v))

        body_bound = bound_vars | set(vars_)
        # Find FORMULA child (skip optional period if present)
        # Structure: [quantifier, var_list, Optional("."), FORMULA] or [quantifier, var_list, FORMULA]
        body_node = k[-1]  # Last child should be FORMULA
        # Verify it's actually a FORMULA by checking if it has FORMULA structure
        if _ename(body_node) != "FORMULA" and not _find_named(body_node, "FORMULA"):
            # If last child is the period token, FORMULA is k[2]
            body_node = k[2] if len(k) > 2 else k[-1]
        out.children.append(pyleri_to_FOLGrammarTreeNode(body_node, body_bound))
        return out

    if rule == "ATOM":
        eq = _find_named(n, "eq_atom")
        if eq is not None:
            return pyleri_to_FOLGrammarTreeNode(eq, bound_vars)
        pred = _find_named(n, "pred_atom")
        if pred is not None:
            return pyleri_to_FOLGrammarTreeNode(pred, bound_vars)
        raise ValueError("ATOM had neither eq_atom nor pred_atom")

    if rule == "pred_atom":
        k = _kids(n)
        pname = k[0].string
        list_node = next((c for c in k if _ecls(c) == "List"), None)
        if list_node is None:
            raise ValueError("pred_atom missing List(...)")
        args = [term(tn, bound_vars) for tn in _list_children_of_name(list_node, "TERM")]
        out = mk(n, "predicate", value=pname)
        out.children.extend(args)
        return out

    if rule == "eq_atom":
        k = _kids(n)
        left = term(k[0], bound_vars)
        right = term(k[2], bound_vars)
        out = mk(n, "equality")
        out.children.extend([left, right])
        return out

    if rule == "NOT":
        k_not_node = _find_named(n, "k_not")
        if k_not_node is None:
            # No negation, just forward the BASE
            return pyleri_to_FOLGrammarTreeNode(_kids(n)[0], bound_vars)
        
        # Find the Sequence containing k_not: Sequence(k_not, BASE)
        seq = None
        for c in _kids(n):
            if _ecls(c) == "Sequence" and _find_named(c, "k_not") is not None:
                seq = c
                break
        
        # If we found the Sequence, BASE is the second child (index 1)
        # Otherwise, look for BASE directly
        if seq and len(_kids(seq)) > 1:
            base = _kids(seq)[1]
        else:
            base = _find_named(n, "BASE")
        
        if base is None:
            raise ValueError("NOT has k_not but no BASE")
        
        out = mk(n, "not")
        out.children.append(pyleri_to_FOLGrammarTreeNode(base, bound_vars))
        return out

    if rule == "AND":
        k = _kids(n)
        first = pyleri_to_FOLGrammarTreeNode(k[0], bound_vars)
        rep = k[1] if len(k) > 1 else None
        rest = [pyleri_to_FOLGrammarTreeNode(_kids(seq)[1], bound_vars) for seq in (_kids(rep) if rep else [])]
        if not rest:
            return first
        out = mk(n, "and")
        out.children = [first] + rest
        return out

    if rule == "OR":
        k = _kids(n)
        first = pyleri_to_FOLGrammarTreeNode(k[0], bound_vars)
        rep = k[1] if len(k) > 1 else None
        rest = [pyleri_to_FOLGrammarTreeNode(_kids(seq)[1], bound_vars) for seq in (_kids(rep) if rep else [])]
        if not rest:
            return first
        out = mk(n, "or")
        out.children = [first] + rest
        return out

    if rule == "IMPL":
        k = _kids(n)
        left = pyleri_to_FOLGrammarTreeNode(k[0], bound_vars)
        opt = k[1] if len(k) > 1 else None
        if not opt or not _kids(opt):
            return left
        seq = _kids(opt)[0]
        right = pyleri_to_FOLGrammarTreeNode(_kids(seq)[1], bound_vars)
        out = mk(n, "implies")
        out.children = [left, right]
        return out

    if rule == "FORMULA" and _ecls(n) == "Sequence":
        k = _kids(n)
        left = pyleri_to_FOLGrammarTreeNode(k[0], bound_vars)
        opt = k[1] if len(k) > 1 else None
        if not opt or not _kids(opt):
            return left
        seq = _kids(opt)[0]
        right = pyleri_to_FOLGrammarTreeNode(_kids(seq)[1], bound_vars)
        out = mk(n, "iff")
        out.children = [left, right]
        return out

    # Handle anonymous Sequence nodes (no rule name) - try to find known structures inside
    if rule is None and _ecls(n) == "Sequence":
        # Check if this Sequence contains k_not - if so, it's part of a NOT structure
        # and we should let the NOT handler process it, not extract BASE directly
        if _find_named(n, "k_not") is not None:
            # This is Sequence(k_not, BASE) - don't extract BASE, let NOT handler deal with it
            # But if we're here, the parent might not be NOT, so check if we should create NOT
            k = _kids(n)
            if len(k) >= 2:
                # Check if first child is k_not
                if _ename(k[0]) in {"k_not"} or (_find_named(k[0], "k_not") is not None):
                    # This is Sequence(k_not, BASE) - create NOT node
                    base = k[1] if len(k) > 1 else None
                    if base:
                        out = mk(n, "not")
                        out.children.append(pyleri_to_FOLGrammarTreeNode(base, bound_vars))
                        return out
        
        # Look for known structures inside this sequence (recursively), but prefer NOT/QUANT/ATOM over BASE
        def find_named_structure(node, prefer_not=False):
            rule_name = _ename(node)
            if rule_name in {"FORMULA", "IMPL", "OR", "AND", "NOT", "QUANT", "ATOM", "pred_atom", "eq_atom"}:
                return node
            if not prefer_not and rule_name == "BASE":
                return node
            for child in _kids(node):
                found = find_named_structure(child, prefer_not)
                if found:
                    return found
            return None
        
        found = find_named_structure(n)
        if found:
            return pyleri_to_FOLGrammarTreeNode(found, bound_vars)
        # If no known structure found, try processing first child
        if _kids(n):
            return pyleri_to_FOLGrammarTreeNode(_kids(n)[0], bound_vars)

    if len(_kids(n)) == 1:
        return pyleri_to_FOLGrammarTreeNode(_kids(n)[0], bound_vars)

    raise ValueError(f"Unhandled rule: {rule}, class={_ecls(n)}, string={getattr(n,'string',None)!r}")


# -------------------------
# 4) Codegen like the paper: get_code + construct_code_sequence
# -------------------------
def get_code(node: FOLGrammarTreeNode, child_vars: TypingList[str]) -> str:
    """
    Return the RHS code (no 'exprN = ' prefix) for this node.
    We'll assign to a fresh exprN in construct_code_sequence.
    """
    t = node.type

    if t == "variable":
        return f"Variable('{node.value}')"
    if t == "constant":
        return f"Constant('{node.value}')"
    if t == "function":
        return f"Function('{node.value}', [{', '.join(child_vars)}])"

    if t == "predicate":
        return f"Predicate('{node.value}', [{', '.join(child_vars)}])"
    if t == "equality":
        # If you don't have Equality(...), replace with: Predicate('Equals', [..])
        return f"Equality({child_vars[0]}, {child_vars[1]})"

    if t == "not":
        return f"Negation({child_vars[0]})"
    if t == "implies":
        return f"Implication({child_vars[0]}, {child_vars[1]})"
    if t == "iff":
        return f"Biconditional({child_vars[0]}, {child_vars[1]})"

    # and/or are handled by folding in construct_code_sequence (because they can be n-ary)
    if t in {"and", "or", "forall", "exists"}:
        raise RuntimeError("get_code should not be called directly for and/or/forall/exists")

    raise ValueError(f"Unknown node type: {t}")


def fol_tree_to_code(tree: FOLGrammarTreeNode, natural_language_statement: TypingOptional[str] = None) -> str:
    """
    Turn FOLGrammarTreeNode into CODE4LOGIC-style python code.
    Similar to paper: post-order traversal + unique expr indices + optional memoization.
    """
    code_sequence: TypingList[str] = []
    formula2var: Dict[Tuple[str, str], str] = {}  # (type, string) -> expr_name
    idx = 0

    if natural_language_statement is not None:
        code_sequence.append(f"natural_language_statement = {natural_language_statement!r}")

    def fresh() -> str:
        nonlocal idx
        idx += 1
        return f"formula{idx}"

    def collect_variables(node: FOLGrammarTreeNode, var_set: Set[str]) -> None:
        """Collect all variable names from the tree."""
        if node.type == "variable" and node.value:
            var_set.add(node.value)
        for child in node.children:
            collect_variables(child, var_set)

    def construct(node: FOLGrammarTreeNode) -> str:
        # For variables, use (type, value) to reuse same-named variables
        # For other nodes, use (type, string) to identify unique formulas
        if node.type == "variable":
            key = (node.type, node.value)
        else:
            key = (node.type, node.string)
        if key in formula2var:
            return formula2var[key]

        # ---- special cases that may be n-ary / need nesting ----
        if node.type in {"and", "or"}:
            # build first child, then fold with the rest
            cur = construct(node.children[0])
            for child in node.children[1:]:
                nxt = construct(child)
                out = fresh()
                if node.type == "and":
                    code_sequence.append(f"{out} = Conjunction({cur}, {nxt})")
                else:
                    code_sequence.append(f"{out} = Disjunction({cur}, {nxt})")
                cur = out
            formula2var[key] = cur
            return cur

        if node.type in {"forall", "exists"}:
            # children are: var(var), var(var), ..., body
            body = construct(node.children[-1])
            vars_ = [c.value for c in node.children[:-1] if c.type == "variable"]

            cur = body
            for v in reversed(vars_):
                # Reuse variable if it already exists (created upfront)
                var_key = ("variable", v)
                if var_key in formula2var:
                    vexpr = formula2var[var_key]
                else:
                    vexpr = fresh()
                    code_sequence.append(f"{vexpr} = Variable('{v}')")
                    formula2var[var_key] = vexpr
                qexpr = fresh()
                if node.type == "forall":
                    code_sequence.append(f"{qexpr} = UniversalQuantification({cur}, '{v}')")
                else:
                    code_sequence.append(f"{qexpr} = ExistentialQuantification({cur}, '{v}')")
                cur = qexpr

            formula2var[key] = cur
            return cur

        # ---- general case: post-order then one assignment ----
        child_vars = [construct(c) for c in node.children]
        out = fresh()
        rhs = get_code(node, child_vars)
        code_sequence.append(f"{out} = {rhs}")
        formula2var[key] = out
        return out

    # First pass: collect all variables and create them upfront
    all_vars: Set[str] = set()
    collect_variables(tree, all_vars)
    
    # Create variable assignments for all variables first (sorted for consistency)
    for v in sorted(all_vars):
        var_key = ("variable", v)
        if var_key not in formula2var:
            vexpr = fresh()
            code_sequence.append(f"{vexpr} = Variable('{v}')")
            formula2var[var_key] = vexpr


    root_var = construct(tree)
    code_sequence.append(f"formula = End({root_var})")
    return "\n".join(code_sequence)


# -------------------------
# 5) Demo
# -------------------------
if __name__ == "__main__":
    g = FOL()
    premise =
    premise_fol = 
    # res = g.parse("forall x. (Teacher(x) -> exists y. (Student(y) and Loves(x, y)))")

#     res = g.parse("""
#     ∀x (DrinkRegularly(x, coffee) → IsDependentOn(x, caffeine)
# """
#     res = g.parse("""
#     ∀x (DrinkRegularly(x, coffee) → IsDependentOn(x, caffeine))
# """
# ∀x (DrinkRegularly(x, coffee) ∨ (¬WantToBeAddictedTo(x, caffeine)))
# ∀x (¬WantToBeAddictedTo(x, caffeine) → ¬AwareThatDrug(x, caffeine))
# ¬(Student(rina) ⊕ ¬AwareThatDrug(rina, caffeine))
# ¬(IsDependentOn(rina, caffeine) ⊕ Student(rina))
# )
    # res = g.parse("∀x (¬WantToBeAddictedTo(x, caffeine) → ¬AwareThatDrug(x, caffeine))")
    res = g.parse("∀x (¬WantToBeAddictedTo(x, caffeine) → ¬AwareThatDrug(x, caffeine))")

    tree = pyleri_to_FOLGrammarTreeNode(res.tree.children[0] if res.tree.children else res.tree)
    pprint(tree)

    # code = fol_tree_to_code(tree, natural_language_statement="Every teacher loves some student.")
    # code = fol_tree_to_code(tree, """All people who regularly drink coffee are dependent on caffeine.
    # """)
    code = fol_tree_to_code(tree, "No one who doesn't want to be addicted to caffeine is unaware that caffeine is a drug.")
# People regularly drink coffee, or they don't want to be addicted to caffeine, or both.
# No one who doesn't want to be addicted to caffeine is unaware that caffeine is a drug.
# Rina is either a student who is unaware that caffeine is a drug, or she is not a student and is she aware that caffeine is a drug.
# Rina is either a student who is dependent on caffeine, or she is not a student and not dependent on caffeine.
    print("\n--- GENERATED CODE ---\n")
    print(code)
