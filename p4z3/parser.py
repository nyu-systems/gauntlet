from p4z3.base import log, z3, P4Range, merge_attrs
from p4z3.base import P4Expression, StructInstance, DefaultExpression
from p4z3.callables import P4Control


MAX_LOOP = 1


class P4Parser(P4Control):
    pass


class RejectState(P4Expression):
    counter = 0

    def reset_counter(self):
        self.counter = 0

    def eval(self, p4_state):
        for context in reversed(p4_state.contexts):
            context.copy_out(p4_state)
        for member_name, _ in p4_state.members:
            member_val = p4_state.resolve_reference(member_name)
            if isinstance(member_val, StructInstance):
                member_val.deactivate("invalid")
        p4_state.has_exited = True


class AcceptState(P4Expression):
    counter = 0

    def reset_counter(self):
        self.counter = 0

    def eval(self, p4_state):
        pass

class ParserTree(P4Expression):

    def __init__(self, states):
        self.states = {}
        for state in states:
            self.states[state.name] = state
        self.states["accept"] = AcceptState()
        self.states["reject"] = RejectState()

    def eval(self, p4_state):
        for state_name, state in self.states.items():
            state.reset_counter()
            p4_state.set_or_add_var(state_name, state, True)
        self.states["start"].eval(p4_state)


class ParserState(P4Expression):

    def __init__(self, name, select, components):
        self.name = name
        self.components = components
        self.select = select
        self.counter = 0
        self.state_list = {}

    def reset_counter(self):
        self.counter = 0

    def eval(self, p4_state):
        if self.counter > MAX_LOOP:
            pass
            # log.warning("Parser exceeded current loop limit, aborting...")
        else:
            select = p4_state.resolve_reference(self.select)
            for component in self.components:
                component.eval(p4_state)
            select.eval(p4_state)


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

    def build_select_cond(self, case_expr, case_name, match_list):
        select_cond = []
        # these casts are kind of silly but simplify the code a lot
        if isinstance(case_expr, StructInstance):
            case_expr = case_expr.flatten()
        elif not isinstance(case_expr, list):
            case_expr = [case_expr]

        for idx, case_match in enumerate(case_expr):
            # default implies don't care, do not add
            # TODO: Verify that this assumption is right...
            if isinstance(case_match, DefaultExpression):
                select_cond.append(z3.BoolVal(True))
            elif isinstance(case_match, P4Range):
                x = case_match.min
                y = case_match.max
                const_name = f"{case_name}_range_{idx}"
                range_const = z3.Const(
                    const_name, match_list[idx].sort())
                c_key_eval = z3.If(range_const <= x, x, z3.If(
                    range_const >= y, y, range_const))
                select_cond.append(c_key_eval == match_list[idx])
            else:
                select_cond.append(case_match == match_list[idx])
        if not select_cond:
            return z3.BoolVal(False)
        return z3.And(*select_cond)

    def eval(self, p4_state):
        switches = []
        select_conds = []
        context = p4_state.current_context()
        forward_cond_copy = context.tmp_forward_cond
        match_list = p4_state.resolve_expr(self.match)

        for case_val, case_name in reversed(self.cases):
            case_expr = p4_state.resolve_expr(case_val)
            cond = self.build_select_cond(case_expr, case_name, match_list)

            # state forks here
            var_store, contexts = p4_state.checkpoint()
            context.tmp_forward_cond = z3.And(forward_cond_copy, cond)
            parser_state = p4_state.resolve_reference(case_name)
            counter = parser_state.counter
            parser_state.counter += 1
            parser_state.eval(p4_state)
            select_conds.append(cond)
            parser_state.counter = counter
            if p4_state.has_exited:
                p4_state.exit_states.append((
                    cond, p4_state.get_z3_repr()))
                p4_state.has_exited = False
            else:
                switches.append((cond, p4_state.get_attrs()))
            p4_state.has_exited = False
            p4_state.restore(var_store, contexts)

        var_store, contexts = p4_state.checkpoint()
        # this hits when the table is either missed, or no action matches
        cond = z3.Not(z3.Or(*select_conds))
        context.tmp_forward_cond = z3.And(forward_cond_copy, cond)
        default_state = p4_state.resolve_reference(self.default)
        counter = default_state.counter
        default_state.counter += 1
        default_state.eval(p4_state)
        if p4_state.has_exited:
            p4_state.exit_states.append((cond, p4_state.get_z3_repr()))
            default_state.counter = counter
            p4_state.restore(var_store, contexts)
        p4_state.has_exited = False
        context.tmp_forward_cond = forward_cond_copy
        for cond, then_vars in switches:
            merge_attrs(p4_state, cond, then_vars)
