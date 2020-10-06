from pprint import pprint
from collections import OrderedDict

# & for disjunction
# + for conjucntion
# -> for implication
# <=> for bi-implication
# ~ for not

binary_connectives = ('&', '|', '->', '<=>')
unary_connectives = ('~',)

def tokenizer(string):
        return string.replace("(", " ( ").replace(")", " ) ").replace("&", " & ").replace("|", " | ").replace("->", " -> ").replace("<=>", " <=> ").replace("~", " ~ ").strip().split()

class Reader():
    def __init__(self, tokens, position=0):
        self.tokens = tokens
        self.position = position

    def next(self):
        self.position += 1
        return self.tokens[self.position-1]

    def peek(self):
        if len(self.tokens) > self.position:
            return self.tokens[self.position]
        else:
            return None

def read_parenthesis(reader):
    array = []
    reader.next()
    token = reader.peek()
    while token != ')':
        if token is None:
            raise Exception("You are missing a \")\".")
        else:
            array.append(read_form(reader))
        token = reader.peek()

    reader.next()
    return array

def read_symbol(reader):
    return reader.next()

def read_form(reader):
    token = reader.peek()
    if token == '(':
        return read_parenthesis(reader)
    else:
        return read_symbol(reader)


def read(string):
    """if string[0] != '(' or string[-1] != ')':
        string = '(' + string + ')'"""
    tokens = tokenizer(string)
    
    reader = Reader(tokens)
    return convert_to_prefix(read_form(reader))

def validate(expr):
    if isinstance(expr, list):
        if len(expr) > 3:
            return False
        elif len(expr) == 3:
            operator, operand_1, operand_2 = expr
            return operator in binary_connectives and validate(operand_1) and validate(operand_2)
        elif len(expr) == 2:
            operator, operand = expr
            return operator == '~' and validate(operand)
        else:
            return False
    else:
        return True

def convert_to_prefix(expr):
    if type(expr) is list:
        if len(expr) == 3:
            operand_1, operator, operand_2 = expr
            return [operator, convert_to_prefix(operand_1), convert_to_prefix(operand_2)]
        elif len(expr) == 2:
            operator, operand = expr
            return [operator, convert_to_prefix(operand)]
        else:
            return [convert_to_prefix(expr[0])]
    else:
        return expr

def pprint_expr(expr):
    string = ""
    if type(expr) is list:
        string += "("
        if len(expr) == 3:
            string += pprint_expr(expr[1])
            string += expr[0]
            string += pprint_expr(expr[2])
        elif len(expr) == 2:
            string += expr[0]
            string += pprint_expr(expr[1])
        string += ")"
        return string
    else:
        return expr

class Tree:
    def __init__(self, data, left=None, right=None):
        self.data = data
        self.left = left
        self.right = right

    def data_as_str(self):
        if type(self.data) == list:
            return ", ".join(pprint_expr(expr).replace("&", "∧").replace("|","∨").replace("->", "→").replace("<=>","↔").replace("~", "¬") for expr in self.data)
        else:
            return self.data

def is_literal(formula):
    if type(formula) is list:
        if len(formula) == 2:
            return type(formula[1]) is not list
        else:
            return False
    return True

def contains_only_literals(tree):
    formulas = tree.data
    for formula in formulas:
        if not is_literal(formula):
            return False
    else:
        return True

def is_closed(tree):
    formulas = tree.data
    for f1 in formulas:
        if type(f1) is not list:
            for f2 in formulas:
                if len(f2) == 2:
                    if f1 == f2[1]:
                        return True
    else:
        return False

def get_first_non_literal(tree):
    formulas = list(tree.data)
    flag = False
    idx = None
    for i, formula in enumerate(formulas):
        if not is_literal(formula):
            idx = i
            flag = True
            break

    if flag:
        f = formulas.pop(idx)
        return f, formulas
    else:
        return None, None

def negate(formula):
    return ['~', formula]

def conjunct(a, b):
    return ['|', a, b]

def disjunct(a, b):
    return ['&', a, b]

def implies(a, b):
    return ['->', a, b]

def iff(a, b):
    return ['<=>', a, b]

def create_tableau(formulas):
    tree = Tree(formulas)
    return extend_tableau(tree)

def extend_tableau(tree):
    if contains_only_literals(tree):
        if is_closed(tree):
            tree.left = Tree("closed")
            return tree
        else:
            tree.left = Tree("open")
            return tree
    else:
        non_literal, formulas = get_first_non_literal(tree)
        if len(non_literal) == 3:
            if non_literal[0] == '&':
                formulas = formulas + [non_literal[1], non_literal[2]]
                tree.left = extend_tableau(Tree(formulas))
                return tree
            if non_literal[0] == '|':
                operand_1, operand_2 = non_literal[1:]
                tree.left = extend_tableau(Tree(formulas + [operand_1]))
                tree.right = extend_tableau(Tree(formulas + [operand_2]))
                return tree
            if non_literal[0] == '->':
                operand_1, operand_2 = non_literal[1:]
                tree.left = extend_tableau(Tree(formulas + [negate(operand_1)]))
                tree.right = extend_tableau(Tree(formulas + [operand_2]))
                return tree
            if non_literal[0] == '<=>':
                operand_1, operand_2 = non_literal[1:]
                left = [disjunct(operand_1, operand_2)]
                right = [disjunct(negate(operand_1), negate(operand_2))]
                tree.left = extend_tableau(Tree(formulas + left))
                tree.right = extend_tableau(Tree(formulas + right))
                return tree
        if len(non_literal) == 2:
            _, inner = non_literal
            if len(inner) == 3:
                if inner[0] == '&':
                    operand_1, operand_2 = inner[1:]
                    tree.left = extend_tableau(Tree(formulas + [negate(operand_1)]))
                    tree.right = extend_tableau(Tree(formulas + [negate(operand_2)]))
                    return tree
                if inner[0] == '|':
                    operand_1, operand_2 = inner[1:]
                    tree.left = extend_tableau(Tree(formulas + [negate(operand_1), negate(operand_2)]))
                    return tree
                if inner[0] == '->':
                    operand_1, operand_2 = inner[1:]
                    tree.left = extend_tableau(Tree(formulas + [operand_1, negate(operand_2)]))
                    return tree
                if inner[0] == '<=>':
                    operand_1, operand_2 = inner[1:]
                    left = [disjunct(operand_1, negate(operand_2))]
                    right = [disjunct(negate(operand_1), operand_2)]
                    tree.left = extend_tableau(Tree(formulas + left))
                    tree.right = extend_tableau(Tree(formulas + right))
                    return tree
            if len(inner) == 2:
                tree.left = extend_tableau(Tree(formulas + [inner[1]]))
                return tree

def print_tree(tree, prefix="", last=True):
    print(prefix, "`- " if last else "|- ", tree.data_as_str(), sep="")
    prefix += "   " if last else "|  "
    children = [tree.left, tree.right]
    children = list(filter(lambda a: a is not None, children))
    child_count = len(children)
    for i, child in enumerate(children):
        last = i == (child_count - 1)
        print_tree(child, prefix, last)

def get_all_leaf_nodes(tree):
    leafs = []
    def _get_all_leaf_nodes(tree):
        if tree is not None:
            if tree.left is None and tree.right is None:
                leafs.append(tree.data)
            _get_all_leaf_nodes(tree.left)
            _get_all_leaf_nodes(tree.right)
    _get_all_leaf_nodes(tree)
    return leafs

def is_tableau_satisfiable(tree):
    leafs = get_all_leaf_nodes(tree)
    for leaf in leafs:
        if leaf == 'open':
            return True
    else:
        return False

def check_binary_connectives(string):
    for binary_connective in binary_connectives:
        if binary_connective in string:
            return True
    else:
        return False

def check_unary_connectives(string):
    return "~" in string

def wff_check_1(string):
    if string[0] != "(" or string[-1] != ')':
        if check_binary_connectives(string):
            return True
        elif check_unary_connectives(string):
            return True
        return False
    return False

def wff_check_2(exprs):
    for expr in exprs:
        if validate(expr):
            return True
    else:
        return False

def READ(string):
    if wff_check_1(string):
        raise Exception("Not a well formed formula.")
    else:
        return read(string)

def EVAL(exprs):
    if not wff_check_2(exprs):
        raise Exception("Not a well formed formula.")
    else:
        return create_tableau(exprs)

def PRINT(tableau, satisfiable_message='Tableau is open, hence is satisfiable.', unsatisfiable_message='Tableau is closed, hence unsatisfiable.'):
    print_tree(tableau)
    if is_tableau_satisfiable(tableau):
        print(satisfiable_message)
    else:
        print(unsatisfiable_message)

def repl():
    """try:
        expr = READ()
        tableau = EVAL([expr])
        PRINT(tableau)
    except Exception as exc:
        print(exc)"""
    string = input('> ')
    if '|=' in string:
        premises, conclusion = string.split('|=')
        premises = premises.strip()
        conclusion = conclusion.strip()
        premise_list = [premise.strip() for premise in premises.split(',')]
        premise_expr_list = [READ(premise) for premise in premise_list]
        conclusion_expr = READ(conclusion)
        neg_conclusion_expr = negate(conclusion_expr)
        premise_conclusion_expr_list = premise_expr_list + [neg_conclusion_expr]
        tableau = EVAL(premise_conclusion_expr_list)
        premises_fmtd = ', '.join(pprint_expr(expr) for expr in premise_expr_list)
        conclusion_fmtd = pprint_expr(conclusion_expr)
        satisfiable_message = premises_fmtd + " does not entail " + conclusion_fmtd + "."
        unsatisfiable_message = premises_fmtd + " entails " + conclusion_fmtd + "."
        PRINT(tableau, satisfiable_message, unsatisfiable_message)
    else:
        expr = READ(string)
        tableau = EVAL([negate(expr)])
        satisfiable_message = pprint_expr(expr) + " is not valid."
        unsatisfiable_message = pprint_expr(expr) + " is valid."
        PRINT(tableau, satisfiable_message, unsatisfiable_message)


def main():
    print("Welcome to the python semantic tableau validity solver.")
    print("If you enter only one proposition, this will check for the validity of that proposition.")
    print("For example, (p|(~p))")
    print("If you want to test an argument with premises and conclusion, use |= to separate the premises from the conclusion, and use commas to separate the premises.")
    print("For example, p|q, ~p |= q")
    print("Enter \"quit\" to quit.")
    while True:
        repl()

if __name__ == '__main__':
    main()
