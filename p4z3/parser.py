from p4z3.base import log, copy, z3
from p4z3.base import P4Expression, P4ComplexInstance
from p4z3.callables import P4Control


MAX_LOOP = 15


class P4Parser(P4Control):
    pass


class P4Exit(P4Expression):

    def eval(self, p4_state):
        # Exit the chain early and absolutely
        p4_state.clear_expr_chain()
        return p4_state.get_z3_repr()


class ParserTree(P4Expression):

    def __init__(self, states):
        self.states = {}
        self.exit_states = ["accept", "reject"]
        for state in states:
            state_name = state.name
            self.states[state_name] = state

    def eval(self, p4_state):
        for state_name, state in self.states.items():
            p4_state.set_or_add_var(state_name, state)
        for state_name in self.exit_states:
            p4_state.set_or_add_var(state_name, P4Exit())
        return self.states["start"].eval(p4_state)


class ParserState(P4Expression):

    def __init__(self, name, select, components):
        self.name = name
        self.components = components
        self.select = select
        self.counter = 0

    def eval(self, p4_state):
        if self.counter > MAX_LOOP:
            log.warning("Parser exceeded current loop limit, aborting...")
            p4_state.clear_expr_chain()
        else:
            self.counter += 1
            select = p4_state.resolve_reference(self.select)
            self.components.append(select)
            p4_state.insert_exprs(self.components)
        p4z3_expr = p4_state.pop_next_expr()
        return p4z3_expr.eval(p4_state)


class ParserSelect(P4Expression):
    def __init__(self, match, *cases):
        self.match = match
        self.cases = []
        self.default = "accept"
        for case_key, case_state in cases:
            if str(case_key) == "default":
                self.default = case_state
            else:
                self.cases.append((case_key, case_state))

    def eval(self, p4_state):
        p4_state_cpy = copy.copy(p4_state)
        expr = p4_state.resolve_expr(self.default)
        for case_val, case_name in reversed(self.cases):
            case_expr = p4_state.resolve_expr(case_val)
            select_cond = []
            if isinstance(case_expr, P4ComplexInstance):
                case_expr = case_expr.flatten()
            if isinstance(case_expr, list):
                for idx, case_match in enumerate(case_expr):
                    match = self.match[idx]
                    match_expr = p4_state.resolve_expr(match)
                    cond = match_expr == case_match
                    select_cond.append(cond)
            else:
                for match in self.match:
                    match_expr = p4_state.resolve_expr(match)
                    cond = case_expr == match_expr
                    select_cond.append(cond)
            if not select_cond:
                select_cond = [z3.BoolVal(False)]
            state_expr = copy.copy(p4_state_cpy).resolve_expr(case_name)
            expr = z3.If(z3.And(*select_cond), state_expr, expr)

        return expr
