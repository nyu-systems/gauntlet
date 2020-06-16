from p4z3.base import OrderedDict, z3, log, copy, copy_attrs, deque
from p4z3.base import merge_parameters, gen_instance, z3_cast, save_variables
from p4z3.base import P4Z3Class, P4ComplexInstance, P4Extern
from p4z3.base import DefaultExpression, P4ComplexType, P4Expression
from p4z3.expressions import P4Mux


class P4Callable(P4Z3Class):
    def __init__(self, name, z3_reg, params, body=[]):
        self.name = name
        self.z3_reg = z3_reg
        self.statements = body
        self.params = params
        self.call_counter = 0
        self.locals = {}

    def eval_callable(self, p4_state, merged_args, var_buffer):
        raise NotImplementedError("Method eval_callable not implemented!")

    def eval(self, p4_state, *args, **kwargs):
        merged_args = merge_parameters(self.params, *args, **kwargs)
        var_buffer = save_variables(p4_state, merged_args)
        expr = self.eval_callable(p4_state, merged_args, var_buffer)
        self.call_counter += 1

        context = p4_state.contexts[-1]
        while context.return_states:
            cond, return_attrs = context.return_states.pop()
            p4_state.merge_attrs(cond, return_attrs)
        context = p4_state.contexts.pop()
        context.restore_context(p4_state)
        return expr

    def __call__(self, p4_state, *args, **kwargs):
        return self.eval(p4_state, *args, **kwargs)

    def set_context(self, p4_state, merged_args, ref_criteria):
        param_buffer = OrderedDict()
        for param_name, arg in merged_args.items():
            # Sometimes expressions are passed, resolve those first
            arg_expr = p4_state.resolve_expr(arg.p4_val)
            # for now use the param name, not the arg_name constructed here
            # FIXME: there are some passes that rename causing issues
            arg_name = f"{self.name}_{param_name}"
            # it can happen that we receive a list
            # infer the type, generate, and set
            if isinstance(arg_expr, list):
                # if the type is undefined, do nothing
                if isinstance(arg.p4_type, P4ComplexType):
                    arg_instance = gen_instance("arg_name", arg.p4_type)
                    arg_instance.set_list(arg_expr)
                    arg_expr = arg_instance
            if arg.is_ref == "inout":
                if isinstance(arg_expr, P4ComplexInstance):
                    arg_expr = copy.copy(arg_expr)
            if arg.is_ref == "out":
                # outs are left-values so the arg must be a string
                # infer the type value at runtime, param does not work yet
                # outs reset the input
                # In the case that the instance is a complex type make sure
                # to propagate the variable through all its members
                log.debug("Resetting %s to %s", arg_expr, param_name)
                if isinstance(arg_expr, P4ComplexInstance):
                    arg_expr = arg_expr.p4z3_type.instantiate("undefined")
                    # FIXME: This should not be needed
                    arg_expr.deactivate()
                else:
                    arg_expr = z3.Const(f"undefined", arg_expr.sort())
            log.debug("Copy-in: %s to %s", arg_expr, param_name)
            # it is possible to pass an int as value, we need to cast it
            if isinstance(arg_expr, int) and isinstance(arg.p4_type, (z3.BitVecSortRef, z3.BitVecRef)):
                arg_expr = z3_cast(arg_expr, arg.p4_type)
            # buffer the value, do NOT set it yet
            param_buffer[param_name] = arg_expr
        # now we can set the arguments without influencing subsequent variables
        for param_name, param_val in param_buffer.items():
            p4_state.set_or_add_var(param_name, param_val)

class MethodCallExpr(P4Expression):

    def __init__(self, p4_method, type_args, *args, **kwargs):
        self.p4_method = p4_method
        self.args = args
        self.kwargs = kwargs
        self.type_args = type_args

    def eval(self, p4_state):
        p4_method = self.p4_method
        # if we get a reference just try to find the method in the state
        if not callable(p4_method):
            p4_method = p4_state.resolve_expr(p4_method)
        # TODO: Figure out how these type bindings work
        if isinstance(p4_method, P4Method) and self.type_args:
            p4_method = p4_method.initialize(*self.type_args)
        expr = p4_method(p4_state, *self.args, **self.kwargs)
        return expr

class ConstCallExpr(P4Expression):

    def __init__(self, p4_method, *args, **kwargs):
        self.p4_method = p4_method
        self.args = args
        self.kwargs = kwargs

    def eval(self, p4_state):
        p4_method = self.p4_method
        if isinstance(p4_method, (P4Control, P4Package)):
            expr = p4_method(*self.args, **self.kwargs)
        else:
            expr = p4_method(p4_state, *self.args, **self.kwargs)
        return expr


class P4Package():

    def __init__(self, z3_reg, name, params):
        self.pipes = OrderedDict()
        self.params = params
        self.name = name
        self.z3_reg = z3_reg

    def init_type_params(self, *args, **kwargs):
        return self

    def initialize(self, *args, **kwargs):
        merged_args = merge_parameters(self.params, *args, **kwargs)
        for pipe_name, pipe_arg in merged_args.items():
            log.info("Loading %s pipe...", pipe_name)
            pipe_val = pipe_arg.p4_val
            if isinstance(pipe_val, ConstCallExpr):
                p4_method_obj = pipe_val.p4_method
                params = p4_method_obj.params
                obj_name = p4_method_obj.name
                p4_state = self.z3_reg.init_p4_state(pipe_name, params)
                pipe = pipe_val.eval(p4_state)

                if isinstance(pipe, P4Control):
                    # initialize with its own params
                    args = []
                    for param in params:
                        args.append(param.name)
                    pipe.apply(p4_state, *args)
                    state = p4_state.get_z3_repr()
                    for exit_cond, exit_state in reversed(p4_state.exit_states):
                        state = z3.If(exit_cond, exit_state, state)
                    self.pipes[pipe_name] = state
                elif isinstance(pipe, P4Extern):
                    self.pipes[pipe_name] = pipe.const
                elif isinstance(pipe, P4Package):
                    # execute the package by calling it
                    pipe.initialize()
                    # resolve all the sub_pipes
                    for sub_pipe_name, sub_pipe_val in pipe.pipes.items():
                        sub_pipe_name = f"{pipe_name}_{sub_pipe_name}"
                        self.pipes[sub_pipe_name] = sub_pipe_val
                else:
                    raise RuntimeError(
                        f"Unsupported value {pipe}, type {type(pipe)}."
                        " It does not make sense as a P4 pipeline.")
            elif isinstance(pipe_val, str):
                pipe = self.z3_reg._globals[pipe_val]
                # execute the package by calling it
                pipe.initialize()
                # resolve all the sub_pipes
                for sub_pipe_name, sub_pipe_val in pipe.pipes.items():
                    sub_pipe_name = f"{pipe_name}_{sub_pipe_name}"
                    self.pipes[sub_pipe_name] = sub_pipe_val
            elif isinstance(pipe_val, z3.ExprRef):
                # for some reason simple expressions are also possible.
                self.pipes[pipe_name] = pipe_val
            else:
                raise RuntimeError(
                    f"Unsupported value {pipe_val}, type {type(pipe_val)}."
                    " It does not make sense as a P4 pipeline.")
        return self

    def __call__(self, *args, **kwargs):
        # TODO Figure out what to actually do here
        return self

    def get_pipes(self):
        return self.pipes


class P4Context(P4Z3Class):

    def __init__(self, var_buffer):
        self.var_buffer = var_buffer
        self.return_states = deque()
        self.has_returned = False
        self.then_has_returned = False
        self.else_has_returned = False
        self.return_exprs = deque()
        self.forward_conds = deque()
        self.tmp_forward_cond = z3.BoolVal(True)

    def add_to_buffer(self, var_dict):
        self.var_buffer = {**self.var_buffer, **var_dict}

    def prepend_to_buffer(self, var_dict):
        self.var_buffer = {**var_dict, **self.var_buffer}

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
        p4_state.check_validity()

    def eval(self, p4_state):
        self.restore_context(p4_state)


class P4Action(P4Callable):

    def eval_callable(self, p4_state, merged_args, var_buffer):
        # actions can modify global variables so do not save the p4 state
        # the only variables that do need to be restored are copy-ins/outs
        context = P4Context(var_buffer)

        self.set_context(p4_state, merged_args, ("out"))

        # execute the action expression with the new environment
        p4_state.contexts.append(context)
        self.statements.eval(p4_state)


class P4Function(P4Action):

    def __init__(self, name, z3_reg, params, return_type, body):
        self.return_type = return_type
        super(P4Function, self).__init__(name, z3_reg, params, body)

    def eval_callable(self, p4_state, merged_args, var_buffer):
        # At the end of the execution a value is returned, NOT the p4 state
        # if the function is part of a method-call statement and the return
        # value is ignored, the method-call statement will continue execution
        context = P4Context(var_buffer)
        self.set_context(p4_state, merged_args, ("out"))

        # execute the action expression with the new environment
        p4_state.contexts.append(context)
        self.statements.eval(p4_state)
        return_expr = None
        if len(context.return_exprs) == 1:
            _, return_expr = context.return_exprs.pop()
        elif len(context.return_exprs) > 1:
            return_cond, return_expr = context.return_exprs.pop()
            if isinstance(return_expr, P4ComplexInstance):
                while context.return_exprs:
                    then_cond, then_expr = context.return_exprs.pop()
                    return_expr = P4Mux(then_cond, then_expr, return_expr)
                return_expr = return_expr.eval(p4_state)
            else:
                while context.return_exprs:
                    then_cond, then_expr = context.return_exprs.pop()
                    return_expr = z3.If(then_cond, then_expr, return_expr)
        return return_expr


class P4Control(P4Callable):

    def __init__(self, name, z3_reg, params, const_params, body, local_decls):
        super(P4Control, self).__init__(name, z3_reg, params, body)
        self.local_decls = local_decls
        self.const_params = const_params
        self.merged_consts = OrderedDict()
        self.locals["apply"] = self.apply

    def init_type_params(self, *args, **kwargs):
        for idx, c_param in enumerate(self.const_params):
            c_param.p4_type = args[idx]
        return self

    def initialize(self, *args, **kwargs):
        self.merged_consts = merge_parameters(
            self.const_params, *args, **kwargs)
        return self

    def __call__(self, *args, **kwargs):
        return self.initialize(*args, **kwargs)

    def apply(self, p4_state, *args, **kwargs):
        return self.eval(p4_state, *args, **kwargs)

    def eval_callable(self, p4_state, merged_args, var_buffer):
        # initialize the local context of the function for execution
        context = P4Context(var_buffer)

        merged_vars = save_variables(p4_state, self.merged_consts)
        context.prepend_to_buffer(merged_vars)

        self.set_context(p4_state, merged_args, ("out"))

        for const_param_name, const_arg in self.merged_consts.items():
            const_val = const_arg.p4_val
            const_val = p4_state.resolve_expr(const_val)
            p4_state.set_or_add_var(const_param_name, const_val)
        # execute the action expression with the new environment
        p4_state.contexts.append(context)
        for expr in self.local_decls:
            expr.eval(p4_state)
            if p4_state.has_exited or p4_state.contexts[-1].has_returned:
                break
        self.statements.eval(p4_state)


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
            # Sometimes expressions are passed, resolve those first
            arg_expr = p4_state.resolve_expr(arg.p4_val)
            # for now use the param name, not the arg_name constructed here
            # FIXME: there are some passes that rename causing issues
            arg_name = f"{self.name}_{param_name}"
            # it can happen that we receive a list
            # infer the type, generate, and set
            if isinstance(arg_expr, list):
                # if the type is undefined, do nothing
                if isinstance(arg.p4_type, P4ComplexType):
                    arg_instance = gen_instance(arg_name, arg.p4_type)
                    arg_instance.set_list(arg_expr)
                    arg_expr = arg_instance
            if arg.is_ref in ref_criteria:
                # outs are left-values so the arg must be a string
                # infer the type value at runtime, param does not work yet
                # outs reset the input
                # In the case that the instance is a complex type make sure
                # to propagate the variable through all its members
                log.debug("Resetting %s to %s", arg_expr, param_name)
                if isinstance(arg_expr, P4ComplexInstance):
                    # assume that for inout header validity is not touched
                    if arg.is_ref == "inout":
                        arg_expr.bind_to_name(arg_name)
                    else:
                        arg_expr = arg_expr.p4z3_type.instantiate(arg_name)
                    # we do not know whether the expression is valid afterwards
                    arg_expr.propagate_validity_bit()
                else:
                    arg_expr = z3.Const(f"{param_name}", arg_expr.sort())
            log.debug("Copy-in: %s to %s", arg_expr, param_name)
            # it is possible to pass an int as value, we need to cast it
            if isinstance(arg_expr, int) and isinstance(arg.p4_type, (z3.BitVecSortRef, z3.BitVecRef)):
                arg_expr = z3_cast(arg_expr, arg.p4_type)
            # buffer the value, do NOT set it yet
            param_buffer[param_name] = arg_expr
        # now we can set the arguments without influencing subsequent variables
        for param_name, param_val in param_buffer.items():
            p4_state.set_or_add_var(param_name, param_val)

    def __copy__(self):
        cls = self.__class__
        result = cls.__new__(cls)
        result.__dict__.update(self.__dict__)
        result.params = copy.deepcopy(result.params)
        for idx, val in enumerate(result.params):
            result.params[idx] = copy.copy(val)
        return result

    def initialize(self, *args, **kwargs):
        # TODO Figure out what to actually do here
        init_method = copy.copy(self)
        # deepcopy is important to ensure independent type inference
        # the type params sometimes include the return type also
        # it is typically the first value, but is bound somewhere else
        if len(args) < len(init_method.type_params):
            type_list = init_method.type_params[1:]
        else:
            type_list = init_method.type_params
        for idx, t_param in enumerate(type_list):
            if init_method.return_type == t_param:
                init_method.return_type = args[idx]
            for method_param in init_method.params:
                if method_param.p4_type == t_param:
                    method_param.p4_type = args[idx]
        return init_method

    def eval_callable(self, p4_state, merged_args, var_buffer):
        # initialize the local context of the function for execution
        context = P4Context(var_buffer)
        self.set_context(p4_state, merged_args, ("inout", "out"))
        p4_state.contexts.append(context)

        if self.return_type is not None:
            # methods can return values, we need to generate a new constant
            # we generate the name based on the input arguments
            var_name = ""
            # for arg in merged_args.values():
            #     arg = p4_state.resolve_expr(arg.p4_val)
            #     # fold runtime-known values
            #     if isinstance(arg, z3.AstRef):
            #         arg = z3.simplify(arg)
            #     # elif isinstance(arg, list):
            #     #     for idx, member in enumerate(arg):
            #     #         arg[idx] = z3.simplify(member)

            #     # Because we do not know what the extern is doing
            #     # we initiate a new z3 const and
            #     # just overwrite all reference types
            #     # input arguments influence the output behavior
            #     # add the input value to the return constant
            #     var_name += str(arg)
            # If we return something, instantiate the type and return it
            # we merge the name
            # FIXME: We do not consider call order
            # and assume that externs are stateless
            return_instance = gen_instance(
                f"{self.name}", self.return_type)
            if isinstance(return_instance, P4ComplexInstance):
                return_instance.propagate_validity_bit()
            return return_instance


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
        super(P4Table, self).__init__(name, None, {})
        self.keys = []
        self.const_entries = []
        self.actions = OrderedDict()
        self.default_action = None
        self.tbl_action = z3.Int(f"{self.name}_action")
        self.locals["hit"] = z3.BoolVal(False)
        self.locals["miss"] = z3.BoolVal(True)
        self.locals["action_run"] = self
        self.locals["apply"] = self.apply

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
        self.locals["hit"] = hit
        self.locals["miss"] = z3.Not(hit)
        # then execute the table as the next expression in the chain
        # FIXME: I do not think this will work with assignment statements
        # the table is probably applied after the value has been assigned
        self.eval(p4_state)
        return self

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
                # this is a ctrl argument, generate an input
                ctrl_arg = gen_instance(
                    f"{self.name}{param.name}", param.p4_type)
                action_args.append(ctrl_arg)
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
        action_matches = []
        context = p4_state.contexts[-1]
        forward_cond_copy = context.tmp_forward_cond
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
            var_store, contexts = p4_state.checkpoint()
            cond = z3.And(self.locals["hit"], action_match)
            context.tmp_forward_cond = z3.And(forward_cond_copy, cond)
            self.eval_action(p4_state, action_tuple)
            then_vars = copy_attrs(p4_state.locals)
            if not p4_state.has_exited:
                action_exprs.append((cond, then_vars))
            p4_state.has_exited = False
            action_matches.append(action_match)
            p4_state.restore(var_store, contexts)

        # then append dynamic table entries to the constant entries
        for action in reversed(actions.values()):
            p4_action_id = action[0]
            action_name = action[1]
            p4_action_args = action[2]
            action_match = (self.tbl_action == z3.IntVal(p4_action_id))
            action_tuple = (action_name, p4_action_args)
            log.debug("Evaluating action %s...", action_name)
            # state forks here
            var_store, contexts = p4_state.checkpoint()
            cond = z3.And(self.locals["hit"], action_match)
            context.tmp_forward_cond = z3.And(forward_cond_copy, cond)
            self.eval_action(p4_state, action_tuple)
            then_vars = copy_attrs(p4_state.locals)
            if not p4_state.has_exited:
                action_exprs.append((cond, then_vars))
            p4_state.has_exited = False
            action_matches.append(action_match)
            p4_state.restore(var_store, contexts)

        # finally evaluate the default entry
        var_store, contexts = p4_state.checkpoint()
        cond = z3.And(self.locals["hit"], z3.Not(z3.Or(*action_matches)))
        context.tmp_forward_cond = z3.And(context.tmp_forward_cond, cond)
        self.eval_default(p4_state)
        if p4_state.has_exited:
            p4_state.restore(var_store, contexts)
        p4_state.has_exited = False
        context.forward_cond = forward_cond_copy
        # generate a nested set of if expressions per available action
        for cond, then_vars in action_exprs:
            p4_state.merge_attrs(cond, then_vars)

    def eval_callable(self, p4_state, merged_args, var_buffer):
        context = P4Context(var_buffer)
        p4_state.contexts.append(context)
        self.eval_table(p4_state)
