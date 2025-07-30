# Switch order of terms
# Switch order of atoms
#

import itertools

class Pred:
    def __init__(self, name: str, arity: int):
        self.name = name
        self.arity = arity

    def __str__(self):
        return self.name
    
    def __eq__(self, other):
        return self.name == other.name and self.arity == other.arity


class Atom:
    def __init__(self, pred: Pred, terms, permutation = None):
        if len(terms) != pred.arity:
            raise Exception("terms must have same length as pred arity")
        self.pred = pred
        self.terms = terms
        self.permutation = list(range(pred.arity)) if permutation is None else permutation

    def __str__(self):
        terms = list(map(str, self.terms))
        return str(self.pred) + "(" + ", ".join(terms) + ")"

    def permute(self, order: list[int]):
        if len(order) != len(self.terms):
            raise Exception("permute order must have same length as terms")
        return Atom(self.pred, [self.terms[i] for i in order], order)


class Rule:
    def __init__(self, head: Atom, body: list[Atom]):
        self.head = head
        self.body = body

    def __str__(self):
        head = str(self.head)
        body = list(map(str, self.body))
        if len(body) == 0:
            return head + "."
        return head + " :- " + ", ".join(body) + "."

    def permute_body(self, order: list[int]):
        return Rule(self.head, [self.body[i] for i in order])
    
    def permute_head(self, order: list[int]):
        return Rule(self.head.permute(order), self.body)

if __name__ == "__main__":
    p = Pred("PP", 2)
    q = Pred("QQ", 3)
    r = Pred("RR", 3)

    h = Atom(r, ["x", "y", "z"])
    b1 = Atom(p, ["x", "y"])
    b2 = Atom(r, ["x", "y", "z"])

    fact1 = Rule(Atom(p, [1, 2]), [])
    fact2 = Rule(Atom(q, [1, 2, 3]), [])
    facts = [fact1, fact2]
    
    rule = Rule(h, [b1, b2])

    print("Permutations:")
    
    body_term_permutations = []
    for atom in rule.permute_body([1, 0]).body:
        l = []
        for order in itertools.permutations(range(atom.pred.arity)):
            l.append(atom.permute(list(order)))
        body_term_permutations.append(l)
            
    for combination in itertools.product(*body_term_permutations):
        permuted_facts = []
        for fact in facts:
            for atom in combination:
                if fact.head.pred == atom.pred:
                    permuted_fact = fact.permute_head(atom.permutation)
                    permuted_facts.append(permuted_fact)
        
        head = rule.head
        for atom in combination:
            if head.pred == atom.pred:
                head = head.permute(atom.permutation)

        print("\n".join(list(map(str, permuted_facts))))
        print(Rule(head, list(combination)))
        print()

# PP(x, y, z) -> PP(x, y, z, x, y, z) | PP(x, y, z)