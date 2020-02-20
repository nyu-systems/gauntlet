from p4z3.base import OrderedDict, z3, log, copy
from p4z3.base import P4Z3Class, P4ComplexType, P4Member


class P4Callable(P4Z3Class):
    def __init__(self, name, z3_reg, params, body=[]):
        self.name = name
        self.z3_reg = z3_reg
        self.statements = body
        self.params = OrderedDict()
        self.call_counter = 0
        for param in params:
            self._add_parameter(param)

    def _add_parameter(self, param=None):
        if param:
            is_ref = param[0]
            param_name = param[1]
            param_type = param[2]
            param_default = param[3]
            self.params[param_name] = (is_ref, param_type, param_default)

    def merge_parameters(self, params, *args, **kwargs):
        merged_params = {}
        args_len = len(args)
        for idx, (param_name, param_tuple) in enumerate(params.items()):
            is_ref = param_tuple[0]
            param_default = param_tuple[2]
            if idx < args_len:
                merged_params[param_name] = (is_ref, args[idx])
            elif param_default is not None:
                # there is no argument but we have a default value, so use that
                merged_params[param_name] = (is_ref, param_default)

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
                var_buffer[param_name] = (is_ref, copy.deepcopy(param_val))
        return var_buffer

    def __call__(self, p4_state=None, *args, **kwargs):
        # for controls and externs, the state is not required
        # controls can only be executed with apply statements
        if p4_state:
            return self.eval(p4_state, *args, **kwargs)
        return self

    def eval_callable(self, p4_state, merged_params, var_buffer):
        raise NotImplementedError("Method eval_callable not implemented!")

    def set_context(self, p4_state, merged_params, ref_criteria):
        param_buffer = OrderedDict()
        for param_name, param in merged_params.items():
            is_ref = param[0]
            arg = param[1]
            if is_ref in ref_criteria:
                # outs are left-values so the arg must be a string
                arg_name = f"{self.name}_{param_name}"
                # infer the type value at runtime, param does not work yet
                arg_expr = p4_state.resolve_expr(arg)
                # outs reset the input
                # In the case that the instance is a complex type make sure
                # to propagate the variable through all its members
                log.debug("Resetting %s to %s", arg, param_name)
                if isinstance(arg_expr, P4ComplexType):
                    arg = arg_expr.instantiate(arg_name)
                else:
                    arg = z3.Const(f"{param_name}", arg_expr.sort())
            else:
                arg = p4_state.resolve_expr(arg)
            # Sometimes expressions are passed, resolve those first
            log.debug("Copy-in: %s to %s", arg, param_name)
            # buffer the value, do NOT set it yet
            param_buffer[param_name] = arg
        # now we can set the arguments without influencing subsequent variables
        for param_name, param_val in param_buffer.items():
            p4_state.set_or_add_var(param_name, param_val)

    def eval(self, p4_state=None, *args, **kwargs):
        self.call_counter += 1
        merged_params = self.merge_parameters(self.params, *args, **kwargs)
        var_buffer = self.save_variables(p4_state, merged_params)
        return self.eval_callable(p4_state, merged_params, var_buffer)


class P4Context(P4Z3Class):

    def __init__(self, var_buffer, old_p4_state):
        self.var_buffer = var_buffer
        self.old_p4_state = old_p4_state

    def restore_context(self, p4_context):
        if self.old_p4_state:
            log.debug("Restoring original p4 state %s to %s ",
                      p4_context, self.old_p4_state)
            expr_chain = p4_context.expr_chain
            old_p4_state = self.old_p4_state
            old_p4_state.expr_chain = expr_chain
        else:
            old_p4_state = p4_context
        # restore any variables that may have been overridden
        for param_name, param in self.var_buffer.items():
            is_ref = param[0]
            param_val = param[1]
            if is_ref in ("inout", "out"):
                # with copy-out we copy from left to right
                # values on the right override values on the left
                # the var buffer is an ordered dict that maintains this order
                val = p4_context.resolve_reference(param_name)
                log.debug("Copy-out: %s to %s", val, param_val)
                old_p4_state.set_or_add_var(param_val, val)
            else:
                log.debug("Resetting %s to %s", param_name, type(param_val))
                old_p4_state.set_or_add_var(param_name, param_val)

            if param_val is None:
                # value has not existed previously, marked for deletion
                log.debug("Deleting %s", param_name)
                try:
                    old_p4_state.del_var(param_name)
                except AttributeError:
                    log.warning(
                        "Variable %s does not exist, nothing to delete!",
                        param_name)
        return old_p4_state

    def eval(self, p4_state):
        old_p4_state = self.restore_context(p4_state)
        p4z3_expr = old_p4_state.pop_next_expr()
        return p4z3_expr.eval(old_p4_state)


class P4Action(P4Callable):

    def eval_callable(self, p4_state, merged_params, var_buffer):
        # actions can modify global variables so do not save the p4 state
        # the only variables that do need to be restored are copy-ins/outs
        p4_context = P4Context(var_buffer, None)

        self.set_context(p4_state, merged_params, ("out"))

        # execute the action expression with the new environment
        p4_state.insert_exprs(p4_context)
        p4_state.insert_exprs(self.statements)
        # reset to the previous execution chain
        p4z3_expr = p4_state.pop_next_expr()
        return p4z3_expr.eval(p4_state)



class P4Function(P4Action):

    def __init__(self, name, z3_reg, params, return_type, body):
        self.return_type = return_type
        super(P4Function, self).__init__(name, z3_reg, params, body)

    def explore(self, expr):
        if z3.is_app_of(expr, z3.Z3_OP_ITE):
            return self.generate_phi_values(expr)
        member_list = []
        for child in expr.children():
            if isinstance(child, z3.DatatypeRef):
                member_list.extend(self.explore(child))
            else:
                member_list.append(child)
        return member_list

    def generate_phi_values(self, input_expr, conditions=True):
        # the first child is usually the condition
        cond = input_expr.children()[0]
        z3_then = input_expr.children()[1]
        z3_else = input_expr.children()[2]
        z3_then_children = self.explore(z3_then)
        z3_else_children = self.explore(z3_else)
        merged_list = []
        for idx, then_child in enumerate(z3_then_children):
            else_child = z3_else_children[idx]
            if_cond = z3.If(cond, then_child, else_child)
            merged_list.append(z3.simplify(if_cond))
        return merged_list
        # self.generate_phi_values(z3_then, z3.And(conditions, cond))
        # self.generate_phi_values(z3_else, z3.And(conditions, z3.Not(cond)))

    def eval_callable(self, p4_state, merged_params, var_buffer):
        # P4Functions always return so we do not need a context object
        # At the end of the execution a value is returned, NOT the p4 state
        # if the function is part of a method-call statement and the return
        # value is ignored, the method-call statement will continue execution
        p4_context = P4Context(var_buffer, None)

        self.set_context(p4_state, merged_params, ("out"))
        # execute the action expression with the new environment
        old_expr_chain = p4_state.copy_expr_chain()
        p4_state.clear_expr_chain()

        p4_state_copy = copy.copy(p4_state)
        p4_state_copy.insert_exprs(self.statements)
        p4z3_expr = p4_state_copy.pop_next_expr()
        return_value = p4z3_expr.eval(p4_state_copy)

        p4_state.insert_exprs(p4_context)
        p4_state.insert_exprs(self.statements)
        # reset to the previous execution chain
        p4z3_expr = p4_state.pop_next_expr()
        expr = p4z3_expr.eval(p4_state)
        if z3.is_app_of(expr, z3.Z3_OP_ITE):
            phi_values = self.generate_phi_values(expr)
            p4_state_members = p4_state.flatten(return_strings=True)
            for idx, member in enumerate(p4_state_members):
                p4_state.set_or_add_var(member, phi_values[idx])

        p4_state.expr_chain = old_expr_chain
        return return_value


class P4Control(P4Callable):

    def __init__(self, name, z3_reg, params, const_params, body, local_decls):
        super(P4Control, self).__init__(name, z3_reg, params, body)
        self.locals = local_decls
        self.const_params = OrderedDict()
        self.merged_consts = OrderedDict()
        for param in const_params:
            is_ref = param[0]
            const_name = param[1]
            const_type = param[2]
            const_default = param[3]
            self.const_params[const_name] = (is_ref, const_type, const_default)

    def init_type_params(self, *args, **kwargs):
        for idx, (c_name, c_param) in enumerate(self.const_params.items()):
            is_ref = c_param[0]
            const_default = c_param[2]
            self.const_params[c_name] = (is_ref, args[idx], const_default)
        return self

    def initialize(self, *args, **kwargs):
        self.merged_consts = self.merge_parameters(
            self.const_params, *args, **kwargs)
        return self

    def __call__(self, p4_state, *args, **kwargs):
        # for controls and externs, the state is not required
        # controls can only be executed with apply statements
        # when there is no p4 state provided, the control is instantiated
        raise RuntimeError()

    def apply(self, p4_state, *args, **kwargs):
        return self.eval(p4_state, *args, **kwargs)

    def eval_callable(self, p4_state, merged_params, var_buffer):
        # initialize the local context of the function for execution
        if not p4_state:
            # There is no state yet, so use the context of the function
            p4_state = self.z3_reg.init_p4_state(self.name, self.params)
            p4_context = P4Context({}, None)
        else:
            p4_context = P4Context(var_buffer, copy.copy(p4_state))

        for const_param_name, const_val in self.merged_consts.items():
            const_arg = const_val[1]
            const_arg = p4_state.resolve_expr(const_arg)
            p4_state.set_or_add_var(const_param_name, const_arg)
        self.set_context(p4_state, merged_params, ("out"))

        # execute the action expression with the new environment
        p4_state.insert_exprs(p4_context)
        p4_state.insert_exprs(self.statements)
        p4_state.insert_exprs(self.locals)
        p4z3_expr = p4_state.pop_next_expr()
        return p4z3_expr.eval(p4_state)


class P4Extern(P4Callable):
    # TODO: This is quite brittle, requires concrete examination
    def __init__(self, name, z3_reg, type_params=[], methods=[]):
        super(P4Extern, self).__init__(name, z3_reg, params=[])
        self.type_params = type_params
        self.methods = methods
        for method in methods:
            setattr(self, method.name, method)

    def init_type_params(self, *args, **kwargs):
        for idx, t_param in enumerate(self.type_params):
            for method in self.methods:
                if method.return_type == t_param:
                    method.return_type = args[idx]
        return self

    def initialize(self, *args, **kwargs):
        # TODO Figure out what to actually do here
        return self

    def sort(self):
        # FIXME: a hack to allow sort access
        # should not be necessary but externs are currently not complex types
        return z3.DeclareSort(self.name)

    def eval_callable(self, p4_state, merged_params, var_buffer):
        if not p4_state:
            # There is no state yet, so use the context of the function
            p4_state = self.z3_reg.init_p4_state(self.name, self.params)

        self.set_context(p4_state, merged_params, ("inout", "out"))

        p4z3_expr = p4_state.pop_next_expr()
        return p4z3_expr.eval(p4_state)


class P4Method(P4Callable):

    # TODO: This is quite brittle, requires concrete examination
    def __init__(self, name, z3_reg, return_type=None, params=[]):
        super(P4Method, self).__init__(name, z3_reg, params)
        # P4Methods, which are also black-box functions, can have return types
        self.return_type = return_type

    def initialize(self, *args, **kwargs):
        # TODO Figure out what to actually do here
        if len(args) > 0 and self.return_type is not None:
            if len(self.params) == 0:
                self.return_type = args[0]
        return self

    def eval_callable(self, p4_state, merged_params, var_buffer):
        # initialize the local context of the function for execution
        if not p4_state:
            # There is no state yet, so use the context of the function
            p4_state = self.z3_reg.init_p4_state(self.name, merged_params)
            p4_context = P4Context({}, None)
        else:
            p4_context = P4Context(var_buffer, copy.copy(p4_state))
        self.set_context(p4_state, merged_params, ("inout", "out"))

        if self.return_type is not None:
            # methods can return values, we need to generate a new constant
            # we generate the name based on the input arguments
            var_name = ""
            for is_ref, arg_val in merged_params.values():
                arg = p4_state.resolve_expr(arg_val)
                # Because we do not know what the extern is doing
                # we initiate a new z3 const and
                # just overwrite all reference types
                # input arguments influence the output behavior
                # add the input value to the return constant
                var_name.join(str(arg))
            # If we return something, instantiate the type and return it
            # we merge the name
            # FIXME: We do not consider call order
            # and assume that externs are stateless
            return_instance = self.z3_reg.instance(
                f"{self.name}_{var_name}", self.return_type)
            return return_instance
        p4_state.insert_exprs(p4_context)
        p4z3_expr = p4_state.pop_next_expr()
        return p4z3_expr.eval(p4_state)


def resolve_action(action_expr):
    # TODO Fix this roundabout way of getting a P4 Action, super annoying...
    if isinstance(action_expr, P4Z3Class):
        action_name = action_expr.p4_method
        action_args = action_expr.args
    elif isinstance(action_expr, str):
        action_name = action_expr
        action_args = []
    else:
        raise TypeError(
            f"Expected a method call, got {type(action_name)}!")
    return action_name, action_args


class P4Table(P4Callable):

    def __init__(self, name, **properties):
        self.name = name
        self.keys = []
        self.const_entries = []
        self.actions = OrderedDict()
        self.default_action = None
        self.tbl_action = z3.Int(f"{self.name}_action")
        self.hit = z3.BoolVal(False)
        self.miss = z3.BoolVal(True)
        self.action_run = self

        self.add_keys(properties)
        self.add_default(properties)
        self.add_actions(properties)
        self.add_const_entries(properties)

    def add_actions(self, properties):
        if "actions" not in properties:
            return
        for action_expr in properties["actions"]:
            action_name, action_args = resolve_action(action_expr)
            index = len(self.actions) + 1
            self.actions[action_name] = (index, action_name, action_args)

    def add_default(self, properties):
        if "default_action" not in properties:
            # In case there is no default action, the first action is default
            self.default_action = (0, "NoAction", ())
        else:
            def_action = properties["default_action"]
            action_name, action_args = resolve_action(def_action)
            self.default_action = (0, action_name, action_args)

    def add_keys(self, properties):
        if "key" not in properties:
            return
        for table_key in properties["key"]:
            self.keys.append(table_key)

    def add_const_entries(self, properties):
        if "entries" not in properties:
            return
        for entry in properties["entries"]:
            const_keys = entry[0]
            action_expr = entry[1]
            if len(self.keys) != len(const_keys):
                raise RuntimeError("Constant keys must match table keys!")
            action_name, action_args = resolve_action(action_expr)
            self.const_entries.append((const_keys, (action_name, action_args)))

    def apply(self, p4_state):
        # tables are a little bit special since they also have attributes
        # so what we do here is first initialize the key
        self.hit = self.eval_keys(p4_state)
        self.miss = z3.Not(self.hit)
        # then execute the table as the next expression in the chain
        # FIXME: I do not think this will work with assignment statements
        # the table is probably applied after the value has been assigned
        p4_state.insert_exprs(self)
        return self

    def __call__(self, p4_state, *args, **kwargs):
        # tables can only be executed after apply statements
        p4z3_expr = p4_state.pop_next_expr()
        return p4z3_expr.eval(p4_state)

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
        _, action_name, p4_action_args = self.default_action
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
