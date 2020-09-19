from p4z3.base import log, z3, P4Range, merge_attrs, P4Mask, DefaultExpression
from p4z3.base import P4Expression, StructInstance, OrderedDict, resolve_type
from p4z3.base import ParserException, StructType, HeaderStack, merge_dicts
from p4z3.base import P4Context
from p4z3.callables import P4Control


class P4Parser(P4Control):

    def collect_stack_sizes(self, p4_type, sizes):
        # FIXME: This is flawed it will not account for many header stacks
        # This should probably be an addition
        # The assumption is that every loop advances at least one stack
        if isinstance(p4_type, HeaderStack):
            sizes.append(len(p4_type.z3_args))
        if isinstance(p4_type, StructType):
            for _, member_type in p4_type.z3_args:
                self.collect_stack_sizes(member_type, sizes)

    def compute_loop_bound(self, p4_state):
        sizes = []
        for param in self.params:
            p4_type = resolve_type(p4_state, param.p4_type)
            self.collect_stack_sizes(p4_type, sizes)
        if sizes:
            max_size = max(sizes)
        else:
            max_size = 1
        return max_size

    def apply(self, p4_state, *args, **kwargs):
        local_context = {}
        for type_name, p4_type in self.type_context.items():
            local_context[type_name] = resolve_type(p4_state, p4_type)
        p4_state.type_contexts.append(self.type_context)
        # disable unrolling for now, we do not really need it for validation
        # and with it, tests take unpleasantly long
        # self.statements.max_loop = self.compute_loop_bound(p4_state)
        self.eval(p4_state, *args, **kwargs)
        p4_state.type_contexts.pop()


class RejectState(P4Expression):
    name = "reject"

    def eval(self, p4_state):

        # FIXME: This checkpointing should not be necessary
        # Figure out what is going on
        forward_conds = []
        tmp_forward_conds = []
        for context in reversed(p4_state.contexts):
            forward_conds.extend(context.forward_conds)
            tmp_forward_conds.append(context.tmp_forward_cond)
        context = p4_state.current_context()

        cond = z3.And(z3.Not(z3.Or(*forward_conds)),
                      z3.And(*tmp_forward_conds))
        var_store, contexts = p4_state.checkpoint()
        for member_name, _ in p4_state.members:
            member_val = p4_state.resolve_reference(member_name)
            if isinstance(member_val, StructInstance):
                member_val.deactivate()
        p4_state.exit_states.append((cond, p4_state.get_z3_repr()))
        p4_state.restore(var_store, contexts)
        p4_state.has_exited = True
        context.forward_conds.append(context.tmp_forward_cond)


class AcceptState(P4Expression):
    name = "accept"

    def eval(self, p4_state):
        pass


class ParserNode():
    def __init__(self, parser_tree, parser_state, match=None):
        self.parser_state = parser_state
        self.parser_tree = parser_tree
        self.child = None
        self.match = match
        self.default = RejectState()
        self.is_terminal = False

    def set_child(self, child):
        self.child = child

    def add_match(self, match):
        self.match = match

    def add_default(self, default):
        self.default = default

    def handle_select(self, p4_state):
        switches = []
        select_conds = []
        context = p4_state.current_context()
        forward_cond_copy = context.tmp_forward_cond
        match_list = p4_state.resolve_expr(self.match)
        for parser_cond, parser_node in reversed(self.child):
            case_expr = p4_state.resolve_expr(parser_cond)
            cond = build_select_cond(p4_state, case_expr, match_list)
            # state forks here
            var_store, contexts = p4_state.checkpoint()
            context.tmp_forward_cond = z3.And(forward_cond_copy, cond)
            parser_node.eval(p4_state)
            select_conds.append(cond)
            if not p4_state.has_exited:
                switches.append(
                    (context.tmp_forward_cond, p4_state.get_attrs()))
            p4_state.has_exited = False
            context.has_returned = False
            p4_state.restore(var_store, contexts)

        # this hits when the table is either missed, or no action matches
        cond = z3.Not(z3.Or(*select_conds))
        context.tmp_forward_cond = z3.And(forward_cond_copy, cond)
        self.default.eval(p4_state)
        p4_state.has_exited = False
        context.has_returned = False
        context.tmp_forward_cond = forward_cond_copy
        for cond, then_vars in switches:
            merge_attrs(p4_state, cond, then_vars)

    def eval(self, p4_state):
        if self.is_terminal:
            context = p4_state.current_context()
            key = self.parser_state.name
            tmp_forward_conds = []
            for context in reversed(p4_state.contexts):
                tmp_forward_conds.append(context.tmp_forward_cond)
            cond = z3.And(*tmp_forward_conds)
            attrs = p4_state.get_attrs()
            # add the
            if key in self.parser_tree.terminal_nodes:
                orig_cond = self.parser_tree.terminal_nodes[key][0]
                orig_dict = self.parser_tree.terminal_nodes[key][1]
                merge_dicts(orig_dict, cond, attrs)
                cond = z3.And(orig_cond, cond)
                attrs = orig_dict
            self.parser_tree.terminal_nodes[key] = (cond, attrs)
            return

        parser_state = self.parser_state
        try:
            parser_state.eval(p4_state)
            if isinstance(self.child, list):
                # there is a switch case try to untangle it.
                self.handle_select(p4_state)
            elif isinstance(self.child, ParserNode):
                # direct descendant, continue the evaluation
                self.child.eval(p4_state)
        except ParserException:
            RejectState().eval(p4_state)


def print_tree(start_node, indent=0):
    node_str = f"{start_node.parser_state.name}\n"
    tmp_indent = indent + 1
    start_child = start_node.child

    if isinstance(start_child, list):
        for child_cond, child in start_node.child:
            child_str = print_tree(child, tmp_indent)
            node_str += tmp_indent * "  " + " ->"
            if child_cond is not None:
                node_str += f" {start_node.match} == {child_cond} ? : {child_str}"
            else:
                node_str += f" {child_str}"
        child_str = print_tree(start_node.default, tmp_indent)
        node_str += tmp_indent * "  " + f" -> {child_str}"
    elif isinstance(start_child, ParserNode):
        child_str = print_tree(start_child, tmp_indent)
        node_str += tmp_indent * "  " + f" -> {child_str}"

    return node_str


class ParserTree(P4Expression):

    def __init__(self, states):
        self.states = {}
        for state in states:
            self.states[state.name] = state
        self.states["accept"] = AcceptState()
        self.states["reject"] = RejectState()
        self.nodes = OrderedDict()
        self.max_loop = 1
        self.terminal_nodes = {}
        visited_states = set()
        self.start_node = self.get_parser_dag(
            visited_states, self.states["start"])

    def get_parser_dag(self, visited_states, init_state):
        node = ParserNode(self, init_state)
        if isinstance(init_state, (AcceptState, RejectState)):
            return node
        if init_state in visited_states:
            node.is_terminal = True
            return node
        self.nodes[init_state.name] = node
        visited_states.add(init_state)
        select = init_state.select
        if isinstance(select, ParserSelect):
            child_node = []
            node.add_match(select.match)
            for case_key, case_name in select.cases:
                sub_child_node = self.get_parser_dag(
                    set(visited_states), self.states[case_name])
                child_node.append((case_key, sub_child_node))
            default = self.states[select.default]
            node.add_default(self.get_parser_dag(set(visited_states), default))
        elif isinstance(select, str):
            select = self.states[select]
            child_node = self.get_parser_dag(set(visited_states), select)
        else:
            child_node = self.get_parser_dag(set(visited_states), select)
        node.set_child(child_node)
        return node

    def eval(self, p4_state):
        self.start_node.eval(p4_state)
        counter = 0
        while counter < self.max_loop:
            parser_states = []
            terminal_nodes = self.terminal_nodes
            self.terminal_nodes = {}
            for parser_state, (cond, state) in terminal_nodes.items():
                sub_node = self.nodes[parser_state]
                # state forks here
                dummy_context = P4Context({})
                dummy_context.locals = state
                dummy_context.tmp_forward_cond = cond
                p4_state.contexts.append(dummy_context)
                sub_node.eval(p4_state)
                parser_states.append((cond, p4_state.get_attrs()))
                p4_state.contexts.pop()

            for cond, then_vars in parser_states:
                merge_attrs(p4_state, cond, then_vars)
            counter += 1


class ParserState(P4Expression):

    def __init__(self, name, select, components):
        self.name = name
        self.components = components
        self.select = select

    def eval(self, p4_state):
        for component in self.components:
            component.eval(p4_state)


def build_select_cond(p4_state, case_expr, match_list):
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
            match_key = z3.And(
                z3.ULE(x, match_list[idx]), z3.UGE(y, match_list[idx]))
            select_cond.append(match_key)
        elif isinstance(case_match, P4Mask):
            val = p4_state.resolve_expr(case_match.value)
            mask = case_match.mask
            match_key = (val | ~mask) == (match_list[idx] | ~mask)
            select_cond.append(match_key)
        else:
            select_cond.append(case_match == match_list[idx])
    if not select_cond:
        return z3.BoolVal(False)
    return z3.And(*select_cond)


class ParserSelect(P4Expression):
    def __init__(self, match, *cases):
        self.match = match
        self.cases = []
        self.default = "reject"
        for case_key, case_name in cases:
            if isinstance(case_key, DefaultExpression):
                self.default = case_name
                # anything after default is considered unreachable
                break
            self.cases.append((case_key, case_name))
