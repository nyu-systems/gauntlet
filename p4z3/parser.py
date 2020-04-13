from p4z3.base import log, z3
from p4z3.base import P4Expression, P4ComplexInstance, DefaultExpression
from p4z3.callables import P4Control
from p4z3.statements import P4Statement, P4Return


MAX_LOOP = 1


class P4Parser(P4Control):
    pass


class RejectState(P4Statement):

    def eval(self, p4_state):
        p4_state.clear_expr_chain()
        return z3.Const("rejected", p4_state.z3_type)


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
        p4_state.set_or_add_var("accept", P4Return())
        p4_state.set_or_add_var("reject", RejectState())
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
            p4_state.insert_exprs(select)
            p4_state.insert_exprs(self.components)
        p4z3_expr = p4_state.pop_next_expr()
        return p4z3_expr.eval(p4_state)


class ParserSelect(P4Expression):
    def __init__(self, match, *cases):
        self.match = match
        self.cases = []
        self.default = "reject"
        for case_key, case_state in cases:
            if isinstance(case_key, DefaultExpression):
                self.default = case_state
                # anything after default is considered unreachable
                break
            self.cases.append((case_key, case_state))

    def eval(self, p4_state):
        switches = []
        for case_val, case_name in reversed(self.cases):
            case_expr = p4_state.resolve_expr(case_val)
            select_cond = []
            if isinstance(case_expr, P4ComplexInstance):
                case_expr = case_expr.flatten()
            if isinstance(case_expr, list):
                for idx, case_match in enumerate(case_expr):
                    # default implies don't care, do not add
                    # TODO: Verify that this assumption is right...
                    if isinstance(case_match, DefaultExpression):
                        continue
                    match = self.match[idx]
                    match_expr = p4_state.resolve_expr(match)
                    cond = match_expr == case_match
                    select_cond.append(cond)
            else:
                # default implies don't care, do not add
                # TODO: Verify that this assumption is right...
                if isinstance(case_expr, DefaultExpression):
                    continue
                for match in self.match:
                    match_expr = p4_state.resolve_expr(match)
                    cond = case_expr == match_expr
                    select_cond.append(cond)
            if not select_cond:
                select_cond = [z3.BoolVal(False)]
            var_store, chain_copy = p4_state.checkpoint()
            state_expr = p4_state.resolve_expr(case_name)
            p4_state.restore(var_store, chain_copy)
            switches.append((z3.And(*select_cond), state_expr))

        expr = p4_state.resolve_expr(self.default)
        for cond, state_expr in switches:
            expr = z3.If(cond, state_expr, expr)
        return expr
