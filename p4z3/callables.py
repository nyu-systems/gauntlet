from p4z3.base import OrderedDict, z3, log, copy
from p4z3.base import merge_parameters, gen_instance, z3_cast, Z3If
from p4z3.base import P4Z3Class, P4ComplexInstance
from p4z3.base import DefaultExpression, P4ComplexType


class P4Callable(P4Z3Class):
    def __init__(self, name, z3_reg, params, body=[]):
        self.name = name
        self.z3_reg = z3_reg
        self.statements = body
        self.params = params
        self.call_counter = 0
        self.p4_attrs = {}

    def save_variables(self, p4_state, merged_args):
        var_buffer = OrderedDict()
        # save all the variables that may be overridden
        for param_name, arg in merged_args.items():
            is_ref = arg.is_ref
            param_ref = arg.p4_val
            # if the variable does not exist, set the value to None
            try:
                param_val = p4_state.resolve_reference(param_name)
                if not isinstance(param_val, z3.AstRef):
                    param_val = copy.copy(param_val)
                var_buffer[param_name] = (is_ref, param_ref, param_val)
            except KeyError:
                var_buffer[param_name] = (is_ref, param_ref, None)
        return var_buffer

    def __call__(self, p4_state, *args, **kwargs):
        return self.eval(p4_state, *args, **kwargs)

    def eval_callable(self, p4_state, merged_args, var_buffer):
        raise NotImplementedError("Method eval_callable not implemented!")

    def set_context(self, p4_state, merged_args, ref_criteria):
        param_buffer = OrderedDict()
        for param_name, arg in merged_args.items():
            arg_expr = p4_state.resolve_expr(arg.p4_val)
            # for now use the param name, not the arg_name constructed here
            # FIXME: there are some passes that rename causing issues
            arg_name = f"{self.name}_{param_name}"
            if arg.is_ref in ref_criteria:
                # outs are left-values so the arg must be a string
                # infer the type value at runtime, param does not work yet
                # outs reset the input
                # In the case that the instance is a complex type make sure
                # to propagate the variable through all its members
                log.debug("Resetting %s to %s", arg_expr, param_name)
                if isinstance(arg_expr, P4ComplexInstance):
                    arg_expr = arg_expr.p4z3_type.instantiate(param_name)
                    arg_expr.deactivate()
                else:
                    arg_expr = z3.Const(f"undefined", arg_expr.sort())
            # FIXME: Awful code...
            if isinstance(arg_expr, list) and isinstance(arg.p4_type, P4ComplexType):
                instance = arg.p4_type.instantiate(param_name)
                instance.set_list(arg_expr)
                arg_expr = instance
            # Sometimes expressions are passed, resolve those first
            log.debug("Copy-in: %s to %s", arg_expr, param_name)
            if isinstance(arg_expr, int):
                arg_expr = z3_cast(arg_expr, arg.p4_type)
            # buffer the value, do NOT set it yet
            param_buffer[param_name] = arg_expr
        # now we can set the arguments without influencing subsequent variables
        for param_name, param_val in param_buffer.items():
            p4_state.set_or_add_var(param_name, param_val)

    def eval(self, p4_state=None, *args, **kwargs):
        self.call_counter += 1
        merged_args = merge_parameters(self.params, *args, **kwargs)
        var_buffer = self.save_variables(p4_state, merged_args)
        return self.eval_callable(p4_state, merged_args, var_buffer)


class P4Context(P4Z3Class):

    def __init__(self, var_buffer, old_p4_state):
        self.var_buffer = var_buffer

    def restore_context(self, p4_state):
        # FIXME: This does not respect local context
        # local variables are overridden in functions and controls
        # restore any variables that may have been overridden
        for param_name, param in self.var_buffer.items():
            is_ref = param[0]
            param_ref = param[1]
            param_val = param[2]
            if is_ref in ("inout", "out"):
                val = p4_state.resolve_reference(param_name)
            if param_val is None:
                # value has not existed previously, marked for deletion
                log.debug("Deleting %s", param_name)
                p4_state.del_var(param_name)
            else:
                log.debug("Resetting %s to %s", param_name, type(param_val))
                p4_state.set_or_add_var(param_name, param_val)

            if is_ref in ("inout", "out"):
                # with copy-out we copy from left to right
                # values on the right override values on the left
                # the var buffer is an ordered dict that maintains this order
                log.debug("Copy-out: %s to %s", val, param_val)
                p4_state.set_or_add_var(param_ref, val)

    def eval(self, p4_state):
        self.restore_context(p4_state)
        p4z3_expr = p4_state.pop_next_expr()
        return p4z3_expr.eval(p4_state)


class P4Action(P4Callable):

    def eval_callable(self, p4_state, merged_args, var_buffer):
        # actions can modify global variables so do not save the p4 state
        # the only variables that do need to be restored are copy-ins/outs
        p4_context = P4Context(var_buffer, None)

        self.set_context(p4_state, merged_args, ("out"))

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

    def eval_callable(self, p4_state, merged_args, var_buffer):
        # P4Functions always return so we do not need a context object
        # At the end of the execution a value is returned, NOT the p4 state
        # if the function is part of a method-call statement and the return
        # value is ignored, the method-call statement will continue execution
        p4_context = P4Context(var_buffer, None)
        self.set_context(p4_state, merged_args, ("out"))

        old_expr_chain = p4_state.copy_expr_chain()
        p4_state.clear_expr_chain()
        p4_state.insert_exprs(p4_context)
        p4_state.insert_exprs(self.statements)
        p4z3_expr = p4_state.pop_next_expr()
        state_expr = p4z3_expr.eval(p4_state)
        p4_state.expr_chain = old_expr_chain
        # functions cast the returned value down to their actual return type
        # FIXME: We can only cast bitvecs right now
        if isinstance(state_expr, (z3.BitVecSortRef, int)):
            return z3_cast(state_expr, self.return_type)
        else:
            return state_expr


class P4Control(P4Callable):

    def __init__(self, name, z3_reg, params, const_params, body, local_decls):
        super(P4Control, self).__init__(name, z3_reg, params, body)
        self.locals = local_decls
        self.const_params = const_params
        self.merged_consts = OrderedDict()
        self.p4_attrs["apply"] = self.apply

    def init_type_params(self, *args, **kwargs):
        for idx, c_param in enumerate(self.const_params):
            c_param.p4_type = args[idx]
        return self

    def initialize(self, *args, **kwargs):
        self.merged_consts = merge_parameters(
            self.const_params, *args, **kwargs)
        return self

    def apply(self, p4_state, *args, **kwargs):
        return self.eval(p4_state, *args, **kwargs)

    def eval_callable(self, p4_state, merged_args, var_buffer):
        # initialize the local context of the function for execution
        p4_context = P4Context(var_buffer, None)
        for const_param_name, const_arg in self.merged_consts.items():
            const_val = const_arg.p4_val
            const_val = p4_state.resolve_expr(const_val)
            p4_state.set_or_add_var(const_param_name, const_val)
        self.set_context(p4_state, merged_args, ("out"))
        # execute the action expression with the new environment
        p4_state.insert_exprs(p4_context)
        p4_state.insert_exprs(self.statements)
        p4_state.insert_exprs(self.locals)
        p4z3_expr = p4_state.pop_next_expr()
        return p4z3_expr.eval(p4_state)


class P4Method(P4Callable):

    def __init__(self, name, z3_reg, type_params, params):
        super(P4Method, self).__init__(name, z3_reg, params)
        # P4Methods, which are also black-box functions, can have return types
        self.return_type = type_params[0]
        self.type_params = type_params[1]

    def set_context(self, p4_state, merged_args, ref_criteria):
        # we have to subclass because of slight different behavior
        # inout and out parameters are not undefined they are set
        # with a new free constant
        param_buffer = OrderedDict()
        for param_name, arg in merged_args.items():
            arg_expr = p4_state.resolve_expr(arg.p4_val)
            # for now use the param name, not the arg_name constructed here
            # FIXME: there are some passes that rename causing issues
            arg_name = f"{self.name}_{param_name}"
            if arg.is_ref in ref_criteria:
                # outs are left-values so the arg must be a string
                # infer the type value at runtime, param does not work yet
                # outs reset the input
                # In the case that the instance is a complex type make sure
                # to propagate the variable through all its members
                log.debug("Resetting %s to %s", arg_expr, param_name)
                if isinstance(arg_expr, P4ComplexInstance):
                    arg_expr = arg_expr.p4z3_type.instantiate(param_name)
                else:
                    arg_expr = z3.Const(f"{param_name}", arg_expr.sort())
            # FIXME: Awful code...
            if isinstance(arg_expr, list) and isinstance(arg.p4_type, P4ComplexType):
                instance = arg.p4_type.instantiate(param_name)
                instance.set_list(arg_expr)
                arg_expr = instance
            # Sometimes expressions are passed, resolve those first
            log.debug("Copy-in: %s to %s", arg_expr, param_name)
            if isinstance(arg_expr, int):
                arg_expr = z3_cast(arg_expr, arg.p4_type)
            # buffer the value, do NOT set it yet
            param_buffer[param_name] = arg_expr
        # now we can set the arguments without influencing subsequent variables
        for param_name, param_val in param_buffer.items():
            p4_state.set_or_add_var(param_name, param_val)

    def initialize(self, *args, **kwargs):
        # TODO Figure out what to actually do here
        init_method = copy.copy(self)
        if len(args) < len(init_method.type_params):
            type_list = init_method.type_params[1:]
        else:
            type_list = init_method.type_params
        for idx, t_param in enumerate(type_list):
            if init_method.return_type == t_param:
                init_method.return_type = args[idx]
            for method_param in init_method.params:
                method_param.p4_type = args[idx]
        return init_method

    def eval_callable(self, p4_state, merged_args, var_buffer):
        # initialize the local context of the function for execution
        p4_context = P4Context(var_buffer, None)
        self.set_context(p4_state, merged_args, ("inout", "out"))
        p4_context.restore_context(p4_state)

        if self.return_type is not None:
            # methods can return values, we need to generate a new constant
            # we generate the name based on the input arguments
            var_name = ""
            for arg in merged_args.values():
                arg = p4_state.resolve_expr(arg.p4_val)
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
            return_instance = gen_instance(
                f"{self.name}_{var_name}", self.return_type)
            return return_instance
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
        self.p4_attrs = {}
        self.keys = []
        self.const_entries = []
        self.actions = OrderedDict()
        self.default_action = None
        self.tbl_action = z3.Int(f"{self.name}_action")
        self.p4_attrs["hit"] = z3.BoolVal(False)
        self.p4_attrs["miss"] = z3.BoolVal(True)
        self.p4_attrs["action_run"] = self
        self.p4_attrs["apply"] = self.apply

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
        hit = self.eval_keys(p4_state)
        self.p4_attrs["hit"] = hit
        self.p4_attrs["miss"] = z3.Not(hit)
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
            key_match = z3.Const(f"{self.name}_table_key_{index}", key_sort)
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
        for idx, param in enumerate(p4_action.params):
            if idx > p4_action_args_len:
                if isinstance(param.p4_type, z3.SortRef):
                    action_args.append(
                        z3.Const(f"{self.name}{param.name}", param.p4_type))
                else:
                    action_args.append(param.p4_type)
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
        action_exprs = []
        # first evaluate all the constant entries
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
                if isinstance(const_key, DefaultExpression):
                    continue
                c_key_eval = p4_state.resolve_expr(const_keys[index])
                matches.append(key_eval == c_key_eval)
            action_match = z3.And(*matches)
            action_tuple = (action_name, p4_action_args)
            log.debug("Evaluating constant action %s...", action_name)
            # state forks here
            var_store, chain_copy = p4_state.checkpoint()
            action_expr = self.eval_action(p4_state, action_tuple)
            p4_state.restore(var_store, chain_copy)
            action_exprs.append((action_match, action_expr))

        # then append dynamic table entries to the constant entries
        for action in reversed(actions.values()):
            p4_action_id = action[0]
            action_name = action[1]
            p4_action_args = action[2]
            action_match = (self.tbl_action == z3.IntVal(p4_action_id))
            action_tuple = (action_name, p4_action_args)
            log.debug("Evaluating action %s...", action_name)
            # state forks here
            var_store, chain_copy = p4_state.checkpoint()
            action_expr = self.eval_action(p4_state, action_tuple)
            p4_state.restore(var_store, chain_copy)
            action_exprs.append((action_match, action_expr))

        # finally evaluate the default entry
        table_expr = self.eval_default(p4_state)
        default_expr = table_expr
        # generate a nested set of if expressions per available action
        for cond, action_expr in action_exprs:
            table_expr = Z3If(cond, action_expr, table_expr)
        # if we hit return the table expr
        # otherwise just return the default expr
        return Z3If(self.p4_attrs["hit"], table_expr, default_expr)

    def eval(self, p4_state):
        return self.eval_table(p4_state)
