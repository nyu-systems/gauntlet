from p4z3.base import log, z3, P4Range, merge_attrs
from p4z3.base import P4Expression, StructInstance, DefaultExpression
from p4z3.callables import P4Control


MAX_LOOP = 1


class P4Parser(P4Control):
    pass


class RejectState(P4Expression):
    counter = 0

    def eval(self, p4_state):
        forward_conds = []
        tmp_forward_conds = []
        for context in reversed(p4_state.contexts):
            forward_conds.extend(context.forward_conds)
            tmp_forward_conds.append(context.tmp_forward_cond)
        context = p4_state.current_context()
        for member_name, _ in p4_state.members:
            member_val = p4_state.resolve_reference(member_name)
            if isinstance(member_val, StructInstance):
                member_val.deactivate("invalid")

        cond = z3.simplify(z3.And(z3.Not(z3.Or(*forward_conds)),
                                  z3.And(*tmp_forward_conds)))
        if not cond == z3.BoolVal(False):
            p4_state.exit_states.append((cond, p4_state.get_z3_repr()))
            p4_state.has_exited = True
        context.forward_conds.append(context.tmp_forward_cond)


class AcceptState(P4Expression):
    counter = 0

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
            pass
            # log.warning("Parser exceeded current loop limit, aborting...")
        else:
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
        context = p4_state.current_context()
        forward_cond_copy = context.tmp_forward_cond

        for case_val, case_name in reversed(self.cases):
            case_expr = p4_state.resolve_expr(case_val)
            select_cond = []
            if isinstance(case_expr, StructInstance):
                case_expr = case_expr.flatten()
            if isinstance(case_expr, list):
                for idx, case_match in enumerate(case_expr):
                    # default implies don't care, do not add
                    # TODO: Verify that this assumption is right...
                    if isinstance(case_match, DefaultExpression):
                        continue
                    match_expr = p4_state.resolve_expr(self.match[idx])
                    if isinstance(case_match, P4Range):
                        x = case_match.min
                        y = case_match.max
                        const_name = f"{case_name}_range_{idx}"
                        range_const = z3.Const(const_name, match_expr.sort())
                        c_key_eval = z3.If(range_const <= x, x, z3.If(
                            range_const >= y, y, range_const))
                        cond = c_key_eval == match_expr
                    else:
                        cond = case_match == match_expr
                    select_cond.append(cond)
            else:
                # default implies don't care, do not add
                # TODO: Verify that this assumption is right...
                if isinstance(case_expr, DefaultExpression):
                    continue
                for idx, match in enumerate(self.match):
                    match_expr = p4_state.resolve_expr(match)
                    if isinstance(case_expr, P4Range):
                        x = case_expr.min
                        y = case_expr.max
                        const_name = f"{case_name}_range_{idx}"
                        range_const = z3.Const(const_name, match_expr.sort())
                        c_key_eval = z3.If(range_const <= x, x, z3.If(
                            range_const >= y, y, range_const))
                        cond = c_key_eval == match_expr
                    else:
                        cond = case_expr == match_expr
                    select_cond.append(cond)
            if not select_cond:
                select_cond = [z3.BoolVal(False)]

            # state forks here
            var_store, contexts = p4_state.checkpoint()
            cond = z3.And(*select_cond)
            context.tmp_forward_cond = z3.And(forward_cond_copy, cond)
            parser_state = self.state_list[case_name]
            counter = parser_state.counter
            parser_state.counter += 1
            self.state_list[case_name].eval(p4_state)
            parser_state.counter = counter
            if not p4_state.has_exited:
                switches.append((cond, p4_state.get_attrs()))
            p4_state.has_exited = False
            select_conds.append(cond)
            p4_state.restore(var_store, contexts)

        var_store, contexts = p4_state.checkpoint()
        # this hits when the table is either missed, or no action matches
        cond = z3.Not(z3.Or(*select_conds))
        context.tmp_forward_cond = z3.And(forward_cond_copy, cond)
        default_state = self.state_list[self.default]
        counter = default_state.counter
        default_state.counter += 1
        self.state_list[self.default].eval(p4_state)
        if p4_state.has_exited:
            default_state.counter = counter
            p4_state.restore(var_store, contexts)
        p4_state.has_exited = False
        context.tmp_forward_cond = forward_cond_copy
        for cond, then_vars in switches:
            merge_attrs(p4_state, cond, then_vars)
