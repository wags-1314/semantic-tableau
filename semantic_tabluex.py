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
    if type(expr) is list:
        if len(expr) > 3:
            return False
        elif len(expr) == 3:
            operand_1, operator, operand_2 = expr
            return validate(operand_1) and (operator in binary_connectives) and validate(operand_2)
        elif len(expr) == 2:
            operator, operand = expr
            return (operator in unary_connectives) and validate(operand)
        elif len(expr) == 1:
            return validate(expr[0])
        else:
            return False
    else:
        return (expr not in binary_connectives) and (expr not in unary_connectives)

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
        if len(formula) == 3:
            return False
        elif len(formula) == 2:
            if type(formula[1]) is list:
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

def create_tabluex(formulas):
    tree = Tree(formulas)
    return extend_tabluex(tree)

def extend_tabluex(tree):
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
                tree.left = extend_tabluex(Tree(formulas))
                return tree
            if non_literal[0] == '|':
                operand_1, operand_2 = non_literal[1:]
                tree.left = extend_tabluex(Tree(formulas + [operand_1]))
                tree.right = extend_tabluex(Tree(formulas + [operand_2]))
                return tree
            if non_literal[0] == '->':
                operand_1, operand_2 = non_literal[1:]
                tree.left = extend_tabluex(Tree(formulas + [negate(operand_1)]))
                tree.right = extend_tabluex(Tree(formulas + [operand_2]))
                return tree
            if non_literal[0] == '<=>':
                operand_1, operand_2 = non_literal[1:]
                left = [disjunct(operand_1, operand_2)]
                right = [disjunct(negate(operand_1), negate(operand_2))]
                tree.left = extend_tabluex(Tree(formulas + left))
                tree.right = extend_tabluex(Tree(formulas + right))
                return tree
        if len(non_literal) == 2:
            _, inner = non_literal
            if len(inner) == 3:
                if inner[0] == '&':
                    operand_1, operand_2 = inner[1:]
                    tree.left = extend_tabluex(Tree(formulas + [negate(operand_1)]))
                    tree.right = extend_tabluex(Tree(formulas + [negate(operand_2)]))
                    return tree
                if inner[0] == '|':
                    operand_1, operand_2 = inner[1:]
                    tree.left = extend_tabluex(Tree(formulas + [negate(operand_1), negate(operand_2)]))
                    return tree
                if inner[0] == '->':
                    operand_1, operand_2 = inner[1:]
                    tree.left = extend_tabluex(Tree(formulas + [operand_1, negate(operand_2)]))
                    return tree
                if inner[0] == '<=>':
                    operand_1, operand_2 = inner[1:]
                    left = [disjunct(operand_1, negate(operand_2))]
                    right = [disjunct(negate(operand_1), operand_2)]
                    tree.left = extend_tabluex(Tree(formulas + left))
                    tree.right = extend_tabluex(Tree(formulas + right))
                    return tree
            if len(inner) == 2:
                tree.left = extend_tabluex(Tree(formulas + [inner[1]]))
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

def check_binary_connectives_and_no_brackets(string):
    for binary_connective in binary_connectives:
        if binary_connective in string:
            return False
    else:
        return True

def check_unary_connectives_and_no_brackets(string):
    return "~" in string

if __name__ == '__main__':
    print("Welcome to the python semantic tree solver.")
    print("Enter \"quit\" to quit.")
    while True:
        string = input("> ")
        if string == "quit":
            break

        if string[0] != "(" or string[-1] != ')': 
            if check_binary_connectives_and_no_brackets(string):
                print("1Not a well formed formula.")
                continue
            elif check_unary_connectives_and_no_brackets(string):
                print("2Not a well formed formula.")
                continue
        try:
            expr = read(string)
        except err:
            print(err)
            
        if validate(expr):
            print("3Not a well formed formula.")
            continue

        print_tree(create_tabluex([expr]))


