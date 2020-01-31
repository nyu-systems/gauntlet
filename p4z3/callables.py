from p4z3.base import OrderedDict, z3, log, copy
from p4z3.base import P4ComplexType, P4Z3Class, P4Context

from p4z3.expressions import MethodCallExpr
from p4z3.statements import P4Declaration


class P4Callable(P4Z3Class):
    def __init__(self):
        self.statements = []
        self.params = OrderedDict()
        self.call_counter = 0

    def add_stmt(self, stmt):
        self.statements.append(stmt)

    def add_parameter(self, param=None):
        if param:
            is_ref = param[0]
            param_name = param[1]
            param_type = param[2]
            self.params[param_name] = (is_ref, param_type)

    def get_parameters(self):
        return self.params

    def merge_parameters(self, params, *args, **kwargs):
        merged_params = {}
        args_len = len(args)
        for idx, param_name in enumerate(params.keys()):
            is_ref = params[param_name][0]
            if idx < args_len:
                merged_params[param_name] = (is_ref, args[idx])
        for arg_name, arg_val in kwargs.items():
            is_ref = params[arg_name][0]
            merged_params[arg_name] = (is_ref, arg_val)
        return merged_params

    def save_variables(self, p4_state, merged_params):
        var_buffer = OrderedDict()
        # save all the variables that may be overridden
        for param_name, param in merged_params.items():
            is_ref = param[0]
            if is_ref in ("inout", "out"):
                var_buffer[param_name] = param
            else:
                # if the variable does not exist, set the value to None
                try:
                    param_val = p4_state.resolve_reference(param_name)
                except AttributeError:
                    param_val = None
                var_buffer[param_name] = (is_ref, param_val)
        return var_buffer

    def __call__(self, p4_state, *args, **kwargs):
        # for controls and externs, the state is not required
        # controls can only be executed with apply statements
        if p4_state:
            return self.eval(p4_state, *args, **kwargs)
        return self

    def eval_callable(self, p4_state, merged_params, var_buffer):
        pass

    def eval(self, p4_state=None, *args, **kwargs):
        self.call_counter += 1
        merged_params = self.merge_parameters(self.params, *args, **kwargs)
        var_buffer = self.save_variables(p4_state, merged_params)
        return self.eval_callable(p4_state, merged_params, var_buffer)


class P4Action(P4Callable):

    def eval_callable(self, p4_state, merged_params, var_buffer):
        p4_state_cpy = p4_state
        p4_context = P4Context(var_buffer, None)
        param_buffer = OrderedDict()
        for param_name, param in merged_params.items():
            is_ref = param[0]
            arg = param[1]
            log.debug("P4Action: Setting %s as %s ", param_name, arg)
            if is_ref == "out":
                # outs reset the input
                param_sort = self.params[param_name][1]
                arg = z3.Const(f"{param_name}", param_sort)
            else:
                arg = p4_state.resolve_expr(arg)
            # Sometimes expressions are passed, resolve those first
            log.debug("Copy-in: %s to %s", arg, param_name)
            # buffer the value, do NOT set it yet
            param_buffer[param_name] = arg
        # now we can set the arguments without influencing subsequent variables
        for param_name, param_val in param_buffer.items():
            p4_state.set_or_add_var(param_name, param_val)

        # execute the action expression with the new environment
        p4_state.insert_exprs(p4_context)
        p4_state.insert_exprs(self.statements)
        # reset to the previous execution chain
        p4z3_expr = p4_state.pop_next_expr()
        return p4z3_expr.eval(p4_state)


class P4Function(P4Action):

    def __init__(self, return_type):
        self.return_type = return_type
        super(P4Function, self).__init__()

class P4Control(P4Callable):

    def __init__(self, z3_reg, name, params, const_params):
        super(P4Control, self).__init__()
        self.locals = []
        self.statements = []
        self.state_initializer = (z3_reg, name)
        self.const_params = OrderedDict()
        self.merged_consts = OrderedDict()
        for param in params:
            self.add_parameter(param)
        for param in const_params:
            is_ref = param[0]
            const_name = param[1]
            const_type = param[2]
            self.const_params[const_name] = const_type

    def declare_local(self, local_name, local_var):
        decl = P4Declaration(local_name, local_var)
        self.statements.append(decl)

    def __call__(self, p4_state, *args, **kwargs):
        # for controls and externs, the state is not required
        # controls can only be executed with apply statements
        # when there is no p4 state provided, the control is instantiated
        for idx, param_tuple in enumerate(self.const_params.items()):
            const_param_name = param_tuple[0]
            self.merged_consts[const_param_name] = args[idx]
        for arg_name, arg in kwargs.items():
            self.merged_consts[arg_name] = arg
        return self

    def apply(self, p4_state, *args, **kwargs):
        return self.eval(p4_state)

    def eval(self, p4_state=None, *args, **kwargs):
        self.call_counter += 1
        # initialize the local context of the function for execution
        z3_reg = self.state_initializer[0]
        name = self.state_initializer[1]
        p4_state_context = z3_reg.init_p4_state(name, self.params)
        p4_state_cpy = p4_state
        if not p4_state:
            # There is no state yet, so use the context of the function
            p4_state = p4_state_context

        merged_params = self.merge_parameters(self.params, *args, **kwargs)
        var_buffer = self.save_variables(p4_state, merged_params)
        p4_context = P4Context(var_buffer, p4_state_cpy)

        for const_param_name, const_arg in self.merged_consts.items():
            const_arg = p4_state.resolve_expr(const_arg)
            p4_state_context.set_or_add_var(const_param_name, const_arg)

        # override the symbolic entries if we have concrete
        # arguments from the table
        for param_name, param in merged_params.items():
            is_ref = param[0]
            arg = param[1]
            param_sort = self.params[param_name][1]
            if is_ref == "out":
                # outs are left-values so the arg must be a string
                arg_name = arg
                arg_const = z3.Const(f"{param_name}", param_sort)
                # except slices can also be lvalues...
                p4_state.set_or_add_var(arg_name, arg_const)
            # Sometimes expressions are passed, resolve those first
            arg = p4_state.resolve_expr(arg)
            log.debug("P4Control: Setting %s as %s %s",
                      param_name, arg, type(arg))
            p4_state_context.set_or_add_var(param_name, arg)

        # execute the action expression with the new environment
        p4_state_context.expr_chain = p4_state.copy_expr_chain()
        p4_state_context.insert_exprs(p4_context)
        p4_state_context.insert_exprs(self.statements)
        p4z3_expr = p4_state_context.pop_next_expr()
        return p4z3_expr.eval(p4_state_context)


class P4Extern(P4Callable):
    # TODO: This is quite brittle, requires concrete examination
    def __init__(self, name, z3_reg, return_type=None):
        super(P4Extern, self).__init__()
        self.name = name
        self.z3_reg = z3_reg
        # P4Methods, which are also black-box functions, can have return types
        self.return_type = return_type
        self.methods = {}

    def add_method(self, name, method):
        self.methods[name] = method
        setattr(self, name, method)

    def eval(self, p4_state=None, *args, **kwargs):
        self.call_counter += 1
        if not p4_state:
            # There is no state yet, so use the context of the function
            p4_state = self.z3_reg.init_p4_state(self.name, self.params)

        merged_params = self.merge_parameters(self.params, *args, **kwargs)
        # externs can return values, we need to generate a new constant
        # we generate the name based on the input arguments
        var_name = ""
        for param_name, param in merged_params.items():
            is_ref = param[0]
            arg = param[1]
            log.debug("Extern: Setting %s as %s ", param_name, arg)
            # Because we do not know what the extern is doing
            # we initiate a new z3 const and just overwrite all reference types
            # we can assume that arg is a lvalue here (i.e., a string)
            arg_expr = p4_state.resolve_expr(arg)
            # input arguments influence the output behavior
            # add the input value to the return constant
            var_name += str(arg_expr)

            if is_ref in ("inout", "out"):
                # Externs often have generic types until they are called
                # This call resolves the argument and gets its z3 type
                if isinstance(arg_expr, int):
                    arg_type = z3.IntSort()
                else:
                    arg_type = arg_expr.sort()
                name = f"{self.name}_{param_name}"
                extern_mod = z3.Const(name, arg_type)
                instance = self.z3_reg.instance(name, arg_type)
                # In the case that the instance is a complex type make sure
                # to propagate the variable through all its members
                if isinstance(instance, P4ComplexType):
                    instance.propagate_type(extern_mod)
                # Finally, assign a new value to the pass-by-reference argument
                p4_state.set_or_add_var(arg, instance)

        if self.return_type is not None:
            # If we return something, instantiate the type and return it
            # we merge the name
            # FIXME: We do not consider call order
            # and assume that externs are stateless
            return_instance = self.z3_reg.instance(
                f"{self.name}_{var_name}", self.return_type)
            return return_instance
        return p4_state.const


def resolve_action(action_expr):
    # TODO Fix this roundabout way of getting a P4 Action, super annoying...
    if isinstance(action_expr, MethodCallExpr):
        action_name = action_expr.p4_method
        action_args = action_expr.args
    elif isinstance(action_expr, str):
        action_name = action_expr
        action_args = []
    else:
        raise TypeError(
            f"Expected a method call, got {type(action_name)}!")
    return action_name, action_args


class P4Table(P4Z3Class):

    def __init__(self, name):
        self.name = name
        self.keys = []
        self.const_entries = []
        self.actions = OrderedDict()
        self.default_action = None
        self.tbl_action = z3.Int(f"{self.name}_action")
        self.hit = z3.BoolVal(False)

    def add_action(self, action_expr):
        action_name, action_args = resolve_action(action_expr)
        index = len(self.actions) + 1
        self.actions[action_name] = (index, action_name, action_args)

    def add_default(self, action_expr):
        action_name, action_args = resolve_action(action_expr)
        self.default_action = (0, action_name, action_args)

    def add_match(self, table_key):
        self.keys.append(table_key)

    def add_const_entry(self, const_keys, action_expr):

        if len(self.keys) != len(const_keys):
            raise RuntimeError("Constant keys must match table keys!")
        action_name, action_args = resolve_action(action_expr)
        self.const_entries.append((const_keys, (action_name, action_args)))

    def apply(self, p4_state):
        self.hit = self.eval_keys(p4_state)
        return self

    def __call__(self, p4_state, *args, **kwargs):
        # tables can only be executed with apply statements
        return self.eval(p4_state)

    def eval_keys(self, p4_state):
        key_pairs = []
        if not self.keys:
            # there is nothing to match with...
            return z3.BoolVal(False)
        for index, key in enumerate(self.keys):
            key_eval = p4_state.resolve_expr(key)
            key_sort = key_eval.sort()
            key_match = z3.Const(f"{self.name}_key_{index}", key_sort)
            key_pairs.append(key_eval == key_match)
        return z3.And(key_pairs)

    def eval_action(self, p4_state, action_tuple):
        p4_action = action_tuple[0]
        p4_action_args = action_tuple[1]
        p4_action = p4_state.resolve_reference(p4_action)
        if not isinstance(p4_action, P4Action):
            raise TypeError(f"Expected a P4Action got {type(p4_action)}!")
        action_args = []
        p4_action_args_len = len(p4_action_args) - 1
        for idx, (arg_name, param) in enumerate(p4_action.params.items()):
            if idx > p4_action_args_len:
                arg_type = param[1]
                if isinstance(arg_type, z3.SortRef):
                    action_args.append(
                        z3.Const(f"{self.name}{arg_name}", arg_type))
                else:
                    action_args.append(arg_type)
            else:
                action_args.append(p4_action_args[idx])
        return p4_action(p4_state, *action_args)

    def eval_default(self, p4_state):
        if self.default_action is None:
            # In case there is no default action, the first action is default
            default_action = (0, "NoAction", ())
        else:
            default_action = self.default_action
        _, action_name, p4_action_args = default_action
        log.debug("Evaluating default action...")
        return self.eval_action(p4_state,
                                (action_name, p4_action_args))

    def eval_table(self, p4_state):
        actions = self.actions
        const_entries = self.const_entries
        # first evaluate the default entry
        # state forks here
        expr = self.eval_default(copy.copy(p4_state))
        # then wrap constant entries around it
        for const_keys, action in reversed(const_entries):
            action_name = action[0]
            p4_action_args = action[1]
            matches = []
            # match the constant keys with the normal table keys
            # this generates the match expression for a specific constant entry
            for index, key in enumerate(self.keys):
                key_eval = p4_state.resolve_expr(key)
                const_key = const_keys[index]
                # default implies don't care, do not add
                # TODO: Verify that this assumption is right...
                if str(const_key) == "default":
                    continue
                c_key_eval = p4_state.resolve_expr(const_keys[index])
                matches.append(key_eval == c_key_eval)
            action_match = z3.And(*matches)
            action_tuple = (action_name, p4_action_args)
            log.debug("Evaluating constant action %s...", action_name)
            action_expr = self.eval_action(copy.copy(p4_state), action_tuple)
            expr = z3.If(action_match, action_expr, expr)

        # then wrap dynamic table entries around the constant entries
        for action in reversed(actions.values()):
            p4_action_id = action[0]
            action_name = action[1]
            p4_action_args = action[2]
            action_match = (self.tbl_action == z3.IntVal(p4_action_id))
            action_tuple = (action_name, p4_action_args)
            log.debug("Evaluating action %s...", action_name)
            # state forks here
            action_expr = self.eval_action(copy.copy(p4_state), action_tuple)
            expr = z3.If(action_match, action_expr, expr)
        # finally return a nested set of if expressions
        return expr

    def eval(self, p4_state):
        # This is a table match where we look up the provided key
        # If we match select the associated action,
        # else use the default action
        # TODO: Check the exact semantics how default actions can be called
        # Right now, they can be called in either the table match or miss
        tbl_match = self.hit
        table_expr = self.eval_table(p4_state)
        def_expr = self.eval_default(p4_state)
        return z3.If(tbl_match, table_expr, def_expr)
