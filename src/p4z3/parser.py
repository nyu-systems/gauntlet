from collections import OrderedDict
from p4z3.state import P4Context
from p4z3.base import log, z3, P4Range, merge_attrs, P4Mask, DefaultExpression
from p4z3.base import P4Expression, StructInstance, resolve_type
from p4z3.base import ParserException, StructType, HeaderStack, merge_dicts
from p4z3.callables import P4Control
import copy

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

    def compute_loop_bound(self, context):
        sizes = []
        for param in self.params:
            p4_type = resolve_type(context, param.p4_type)
            self.collect_stack_sizes(p4_type, sizes)
        if sizes:
            max_size = max(sizes)
        else:
            max_size = 1
        return max_size

    def apply(self, context, *args, **kwargs):
        for type_name, p4_type in self.type_context.items():
            context.add_type(type_name, resolve_type(context, p4_type))
        # disable unrolling for now, we do not really need it for validation
        # and with it, tests take unpleasantly long
        # self.statements.max_loop = self.compute_loop_bound(context)
        self.eval(context, *args, **kwargs)


class RejectState(P4Expression):
    name = "reject"

    def eval(self, context):
        # FIXME: This checkpointing should not be necessary
        # Figure out what is going on
        forward_conds = []
        tmp_forward_conds = []
        sub_ctx = context
        while sub_ctx is not None:
            forward_conds.extend(sub_ctx.forward_conds)
            tmp_forward_conds.append(sub_ctx.tmp_forward_cond)
            sub_ctx = sub_ctx.parent_context

        cond = z3.And(z3.Not(z3.Or(*forward_conds)),
                      z3.And(*tmp_forward_conds))
        var_store, contexts = context.checkpoint()
        for member_name, _ in context.p4_state.members:
            member_val = context.resolve_reference(member_name)
            if isinstance(member_val, StructInstance):
                member_val.deactivate()
        context.p4_state.exit_states.append(
            (cond, context.p4_state.get_members(context)))
        context.restore(var_store, contexts)
        context.p4_state.has_exited = True
        context.forward_conds.append(context.tmp_forward_cond)


class AcceptState(P4Expression):
    name = "accept"

    def eval(self, context):
        cond = z3.simplify(z3.And(z3.Not(z3.Or(*context.forward_conds)),
                                  context.tmp_forward_cond))
        if not z3.is_false(cond):
            context.return_states.append((cond, context.copy_attrs()))
            context.has_returned = True
        context.forward_conds.append(context.tmp_forward_cond)


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

    def handle_select(self, context):
        switches = []
        select_conds = []
        forward_cond_copy = context.tmp_forward_cond
        match_list = context.resolve_expr(self.match)
        for parser_cond, parser_node in self.child:
            case_expr = context.resolve_expr(parser_cond)
            cond = build_select_cond(context, case_expr, match_list)
            # state forks here
            var_store, contexts = context.checkpoint()
            context.tmp_forward_cond = z3.And(forward_cond_copy, cond)
            parser_node.eval(context)
            select_conds.append(cond)
            if not (context.p4_state.has_exited or z3.is_false(cond)):
                switches.append(
                    (context.tmp_forward_cond, context.get_attrs()))
            context.p4_state.has_exited = False
            context.has_returned = False
            context.restore(var_store, contexts)

        # this hits when no select matches
        cond = z3.Not(z3.Or(*select_conds))
        context.tmp_forward_cond = z3.And(forward_cond_copy, cond)
        self.default.eval(context)
        context.p4_state.has_exited = False
        context.has_returned = False
        context.tmp_forward_cond = forward_cond_copy
        for cond, then_vars in reversed(switches):
            merge_attrs(context, cond, then_vars)

    def eval(self, context):

        parser_state = self.parser_state
        try:
            parser_state.eval(context)
        except ParserException:
            RejectState().eval(context)
            return

        if self.is_terminal:
            key = self.parser_state.name
            tmp_forward_conds = []
            sub_ctx = context
            while sub_ctx is not None:
                tmp_forward_conds.append(sub_ctx.tmp_forward_cond)
                sub_ctx = sub_ctx.parent_context

            cond = z3.And(*tmp_forward_conds)
            attrs = context.get_attrs()
            # add the
            if key in self.parser_tree.terminal_nodes:
                orig_cond = self.parser_tree.terminal_nodes[key][0]
                orig_dict = self.parser_tree.terminal_nodes[key][1]
                merge_dicts(orig_dict, cond, attrs)
                cond = z3.Or(orig_cond, cond)
                attrs = orig_dict
            self.parser_tree.terminal_nodes[key] = (cond, attrs)
            return

        if isinstance(self.child, list):
            # there is a switch case try to untangle it.
            self.handle_select(context)
        elif isinstance(self.child, ParserNode):
            # direct descendant, continue the evaluation
            self.child.eval(context)


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

    def eval(self, context):
        self.start_node.eval(context)
        counter = 0
        while counter < self.max_loop:
            parser_states = []
            terminal_nodes = self.terminal_nodes
            self.terminal_nodes = {}
            for parser_state, (cond, state) in terminal_nodes.items():
                sub_node = self.nodes[parser_state]
                # state forks here
                # FIXME
                dummy_context = P4Context(context.p4_state.static_context, {})
                dummy_context.locals = copy.deepcopy(state)
                dummy_context.tmp_forward_cond = cond
                sub_node.eval(dummy_context)
                parser_states.append((cond, dummy_context.get_attrs()))

            for cond, then_vars in parser_states:
                merge_attrs(context, cond, then_vars)
            counter += 1


class ParserState(P4Expression):

    def __init__(self, name, select, components):
        self.name = name
        self.components = components
        self.select = select

    def eval(self, context):
        for component in self.components:
            component.eval(context)


def build_select_cond(context, case_expr, match_list):
    select_cond = []
    # these casts are kind of silly but simplify the code a lot
    if isinstance(case_expr, StructInstance):
        case_expr = case_expr.flatten(z3.BoolVal(True))
    elif not isinstance(case_expr, list):
        case_expr = [case_expr]

    for idx, case_match in enumerate(case_expr):
        # default implies don't care, do not add
        # TODO: Verify that this assumption is right...
        if isinstance(case_match, DefaultExpression):
            select_cond.append(z3.BoolVal(True))
        elif isinstance(case_match, P4Range):
            x = context.resolve_expr(case_match.min)
            y = context.resolve_expr(case_match.max)
            match_key = z3.And(
                z3.ULE(x, match_list[idx]), z3.UGE(y, match_list[idx]))
            select_cond.append(match_key)
        elif isinstance(case_match, P4Mask):
            val = context.resolve_expr(case_match.value)
            mask = context.resolve_expr(case_match.mask)
            match_key = (val & mask) == (match_list[idx] & mask)
            select_cond.append(match_key)
        else:
            select_cond.append(case_match == match_list[idx])
    if not select_cond:
        return z3.BoolVal(False)
    return z3.And(*select_cond)


class ParserSelect(P4Expression):
    def __init__(self, match, case_list):
        self.match = match
        self.cases = []
        self.default = "reject"
        for case_key, case_name in case_list:
            if isinstance(case_key, DefaultExpression):
                self.default = case_name
                # anything after default is considered unreachable
                break
            self.cases.append((case_key, case_name))
