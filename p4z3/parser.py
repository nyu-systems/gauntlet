from p4z3.base import log, z3, copy_attrs
from p4z3.base import P4Expression, P4ComplexInstance, DefaultExpression
from p4z3.callables import P4Control
from p4z3.statements import P4Statement, P4Return, P4Exit, BlockStatement


MAX_LOOP = 2


class P4Parser(P4Control):
    pass


class RejectState(P4Statement):

    def eval(self, p4_state):
        for context in reversed(p4_state.contexts):
            context.restore_context(p4_state)
        p4_state.deactivate("invalid")
        p4_state.has_exited = True

class AcceptState(P4Statement):

    def eval(self, p4_state):
        pass

class ParserTree(P4Expression):

    def __init__(self, states):
        self.states = {}
        self.exit_states = ["accept", "reject"]
        for state in states:
            state_name = state.name
            self.states[state_name] = state
        self.states["accept"] = AcceptState()
        self.states["reject"] = RejectState()
        for state in states:
            state.set_state_list(self.states)

    def eval(self, p4_state):
        self.states["start"].eval(p4_state)
        for state in self.states.values():
            if isinstance(state, ParserState):
                state.reset_counter()


class ParserState(P4Expression):

    def __init__(self, name, select, components):
        self.name = name
        self.components = components
        self.select = select
        self.counter = 0
        self.state_list = {}

    def set_state_list(self, state_list):
        self.state_list = state_list

    def reset_counter(self):
        self.counter = 0

    def eval(self, p4_state):
        if self.counter > MAX_LOOP:
            log.warning("Parser exceeded current loop limit, aborting...")
        else:
            self.counter += 1
            if isinstance(self.select, ParserSelect):
                select = self.select
                select.set_state_list(self.state_list)
            elif isinstance(self.select, str):
                select = self.state_list[self.select]
            else:
                select = self.select
            for component in self.components:
                component.eval(p4_state)
            if not p4_state.has_exited:
                select.eval(p4_state)


class ParserSelect(P4Expression):
    def __init__(self, match, *cases):
        self.match = match
        self.cases = []
        self.state_list = {}
        self.default = "reject"
        for case_key, case_state in cases:
            if isinstance(case_key, DefaultExpression):
                self.default = case_state
                # anything after default is considered unreachable
                break
            self.cases.append((case_key, case_state))

    def set_state_list(self, state_list):
        self.state_list = state_list

    def eval(self, p4_state):
        switches = []
        select_conds = []
        context = p4_state.contexts[-1]
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
            select_cond = z3.And(*select_cond)
            select_conds.append(select_cond)
            var_store, contexts = p4_state.checkpoint()
            parser_state = self.state_list[case_name]
            has_returned_copy = context.has_returned
            parser_state.eval(p4_state)
            then_vars = copy_attrs(p4_state.locals)
            if p4_state.has_exited:
                p4_state.exit_states.append((
                    select_cond, p4_state.get_z3_repr()))
                p4_state.has_exited = False
            else:
                switches.append((select_cond, then_vars))
            p4_state.restore(var_store, contexts)
            context.has_returned = has_returned_copy
        default_parser_state = self.state_list[self.default]
        var_store, contexts = p4_state.checkpoint()
        default_parser_state.eval(p4_state)
        if p4_state.has_exited:
            cond = z3.Not(z3.Or(*select_conds))
            p4_state.exit_states.append((cond, p4_state.get_z3_repr()))
            p4_state.has_exited = False
            p4_state.restore(var_store, contexts)
        for cond, then_vars in switches:
            p4_state.merge_attrs(cond, then_vars)
