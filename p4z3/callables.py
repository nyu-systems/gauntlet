from p4z3.base import OrderedDict, z3, log, copy, merge_attrs
from p4z3.base import gen_instance, z3_cast, handle_mux, TypeSpecializer
from p4z3.base import P4Z3Class, P4ComplexInstance, P4ComplexType, P4Context
from p4z3.base import DefaultExpression, P4Extern, propagate_validity_bit
from p4z3.base import P4Expression, P4Argument, P4Range, resolve_type, ListType


def save_variables(p4_state, merged_args):
    var_buffer = OrderedDict()
    # save all the variables that may be overridden
    for param_name, arg in merged_args.items():
        try:
            param_val = p4_state.resolve_reference(param_name)
            var_buffer[param_name] = (arg.is_ref, arg.p4_val, param_val)
        except RuntimeError:
            # if the variable name does not exist, set the value to None
            var_buffer[param_name] = (arg.is_ref, arg.p4_val, None)
    return var_buffer


def merge_parameters(params, *args, **kwargs):
    # FIXME: This function could be a lot more efficient...
    # FIXME: Overloading does not work correctly here
    merged_args = {}
    args_len = len(args)
    for idx, param in enumerate(params):
        if idx < args_len:
            arg_val = args[idx]
            if isinstance(arg_val, DefaultExpression):
                # Default expressions are pointless arguments, so skip them
                continue
            arg = P4Argument(param.is_ref, param.p4_type, arg_val)
            merged_args[param.name] = arg
        elif param.p4_default is not None:
            # there is no argument but we have a default value, so use that
            arg_val = param.p4_default
            arg = P4Argument(param.is_ref, param.p4_type, arg_val)
            merged_args[param.name] = arg
    for param_name, arg_val in kwargs.items():
        # this is expensive but at least works reliably
        if isinstance(arg_val, DefaultExpression):
            # Default expressions are pointless arguments, so skip them
            continue
        for param in params:
            if param.name == param_name:
                arg = P4Argument(param.is_ref, param.p4_type, arg_val)
                merged_args[param_name] = arg
    return merged_args


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
            p4_method = p4_method.init_type_params(*self.type_args)

        return p4_method(p4_state, *self.args, **self.kwargs)


class P4Callable(P4Z3Class):
    def __init__(self, name, params, body=[]):
        self.name = name
        self.statements = body
        self.params = params
        self.call_counter = 0
        self.locals = {}

    def eval_callable(self, p4_state, merged_args, var_buffer):
        raise NotImplementedError("Method eval_callable not implemented!")

    def eval(self, p4_state, *args, **kwargs):
        merged_args = merge_parameters(self.params, *args, **kwargs)
        var_buffer = save_variables(p4_state, merged_args)
        param_buffer = self.copy_in(p4_state, merged_args)
        # only add the context after all the arguments have been resolved
        context = P4Context(var_buffer)
        p4_state.contexts.append(context)
        # now we can set the arguments without influencing subsequent variables
        for param_name, param_val in param_buffer.items():
            p4_state.set_or_add_var(param_name, param_val)

        # execute the action expression with the new environment
        expr = self.eval_callable(p4_state, merged_args, var_buffer)
        self.call_counter += 1

        while context.return_states:
            cond, return_attrs = context.return_states.pop()
            merge_attrs(p4_state, cond, return_attrs)
        context.copy_out(p4_state)
        p4_state.contexts.pop()
        return expr

    def __call__(self, p4_state, *args, **kwargs):
        return self.eval(p4_state, *args, **kwargs)

    def copy_in(self, p4_state, merged_args):
        param_buffer = OrderedDict()
        for param_name, arg in merged_args.items():
            # Sometimes expressions are passed, resolve those first
            arg_expr = p4_state.resolve_expr(arg.p4_val)
            # for now use the param name, not the arg_name constructed here
            # FIXME: there are some passes that rename causing issues
            arg_name = f"{self.name}_{param_name}"
            # it can happen that we receive a list
            # infer the type, generate, and set
            p4_type = resolve_type(p4_state, arg.p4_type)
            if isinstance(arg_expr, list):
                # if the type is undefined, do nothing
                if isinstance(p4_type, P4ComplexType):
                    arg_instance = gen_instance(
                        p4_state, "undefined", p4_type)
                    arg_instance.set_list(arg_expr)
                    arg_expr = arg_instance
            # it is possible to pass an int as value, we need to cast it
            elif isinstance(arg_expr, int):
                arg_expr = z3_cast(arg_expr, p4_type)
            if isinstance(arg_expr, P4ComplexInstance):
                arg_expr = copy.copy(arg_expr)
            if arg.is_ref == "out":
                # outs are left-values so the arg must be a string
                # infer the type value at runtime, param does not work yet
                # outs reset the input
                # In the case that the instance is a complex type make sure
                # to propagate the variable through all its members
                log.debug("Resetting %s to %s", arg_expr, param_name)
                arg_expr = gen_instance(p4_state, "undefined", p4_type)

            log.debug("Copy-in: %s to %s", arg_expr, param_name)
            # buffer the value, do NOT set it yet
            param_buffer[param_name] = arg_expr
        return param_buffer

class ConstCallExpr(P4Expression):

    def __init__(self, p4_method, *args, **kwargs):
        self.p4_method = p4_method
        self.args = args
        self.kwargs = kwargs

    def eval(self, p4_state):
        p4_method = resolve_type(p4_state, self.p4_method)
        resolved_args = []
        for arg in self.args:
            resolved_args.append(p4_state.resolve_expr(arg))
        return p4_method.initialize(p4_state, *resolved_args, **self.kwargs)

class P4Package(P4Callable):

    def __init__(self, z3_reg, name, params, type_params):
        super(P4Package, self).__init__(name, params)
        self.pipes = OrderedDict()
        self.z3_reg = z3_reg
        self.type_params = type_params

    def init_type_params(self, *args, **kwargs):
        # TODO Figure out what to actually do here
        return self

    def eval_callable(self, p4_state, merged_args, var_buffer):
        pass

    def initialize(self, context, *args, **kwargs):
        merged_args = merge_parameters(self.params, *args, **kwargs)
        for pipe_name, pipe_arg in merged_args.items():
            log.info("Loading %s pipe...", pipe_name)
            pipe_val = self.z3_reg.p4_state.resolve_expr(pipe_arg.p4_val)
            if isinstance(pipe_val, P4Control):
                ctrl_type = resolve_type(self.z3_reg, pipe_arg.p4_type)
                pipe_val = pipe_val.bind_to_ctrl_type(ctrl_type)

                # create the z3 representation of this control state
                p4_state = self.z3_reg.set_p4_state(pipe_name, pipe_val.params)
                # initialize the call with its own params
                # this is essentially the input packet
                args = []
                for param in pipe_val.params:
                    args.append(param.name)
                pipe_val.apply(p4_state, *args)
                # after executing the pipeline get its z3 representation
                state = p4_state.get_z3_repr()
                # and also merge back all the exit states we collected
                for exit_cond, exit_state in reversed(p4_state.exit_states):
                    state = z3.If(exit_cond, exit_state, state)
                # all done, that is our P4 representation!
                self.pipes[pipe_name] = (state, p4_state.members)
            elif isinstance(pipe_val, P4Extern):
                self.pipes[pipe_name] = (pipe_val.const, [])
            elif isinstance(pipe_val, P4Package):
                # execute the package by calling its initializer
                pipe_val.initialize(context)
                # resolve all the sub_pipes
                for sub_pipe_name, sub_pipe_val in pipe_val.pipes.items():
                    sub_pipe_name = f"{pipe_name}_{sub_pipe_name}"
                    self.pipes[sub_pipe_name] = sub_pipe_val
            elif isinstance(pipe_val, z3.ExprRef):
                # for some reason simple expressions are also possible.
                self.pipes[pipe_name] = (pipe_val, [])
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


class P4Action(P4Callable):

    def eval_callable(self, p4_state, merged_args, var_buffer):
        # actions can modify global variables so do not save the p4 state
        # the only variables that do need to be restored are copy-ins/outs
        self.statements.eval(p4_state)


class P4Function(P4Action):

    def __init__(self, name, params, return_type, body):
        super(P4Function, self).__init__(name, params, body)
        self.return_type = return_type

    def eval_callable(self, p4_state, merged_args, var_buffer):
        # execute the action expression with the new environment
        context = p4_state.current_context()
        context.return_type = self.return_type
        self.statements.eval(p4_state)
        return_expr = None
        if len(context.return_exprs) == 1:
            _, return_expr = context.return_exprs.pop()
        elif len(context.return_exprs) > 1:
            # the first condition is not needed since it is the default
            _, return_expr = context.return_exprs.pop()
            if isinstance(return_expr, P4ComplexInstance):
                while context.return_exprs:
                    then_cond, then_expr = context.return_exprs.pop()
                    return_expr = handle_mux(then_cond, then_expr, return_expr)
            else:
                while context.return_exprs:
                    then_cond, then_expr = context.return_exprs.pop()
                    return_expr = z3.If(then_cond, then_expr, return_expr)
        return return_expr


class P4Control(P4Callable):

    def __init__(self, name, type_params, params, const_params, body, local_decls):
        super(P4Control, self).__init__(name, params, body)
        self.local_decls = local_decls
        self.type_params = type_params
        self.const_params = const_params
        self.merged_consts = OrderedDict()
        self.locals["apply"] = self.apply
        self.type_context = {}

    def bind_to_ctrl_type(self, ctrl_type):
        # FIXME: A hack to deal with lack of input params
        if len(ctrl_type.params) < len(self.type_params):
            return self
        # TODO Figure out what to actually do here
        init_ctrl = copy.copy(self)
        # the type params sometimes include the return type also
        # it is typically the first value, but is bound somewhere else
        for idx, t_param in enumerate(init_ctrl.type_params):
            init_ctrl.type_context[t_param] = ctrl_type.params[idx].p4_type
            for param_idx, param in enumerate(init_ctrl.params):
                if isinstance(param.p4_type, str) and param.p4_type == t_param:
                    init_ctrl.params[param_idx] = ctrl_type.params[idx]
        return init_ctrl

    def init_type_params(self, *args, **kwargs):
        # TODO Figure out what to actually do here
        init_ctrl = copy.copy(self)
        # the type params sometimes include the return type also
        # it is typically the first value, but is bound somewhere else
        for idx, t_param in enumerate(init_ctrl.type_params):
            init_ctrl.type_context[t_param] = args[idx]
            for param in init_ctrl.params:
                if isinstance(param.p4_type, str) and param.p4_type == t_param:
                    param.p4_type = args[idx]
        return init_ctrl

    def initialize(self, context, *args, **kwargs):
        ctrl_copy = copy.copy(self)
        ctrl_copy.merged_consts = merge_parameters(
            ctrl_copy.const_params, *args, **kwargs)
        # also bind types, because for reasons you can bind types everywhere...
        for idx, const_param in enumerate(ctrl_copy.const_params):
            # this means the type is generic
            p4_type = resolve_type(context, const_param.p4_type)
            if p4_type is None:
                # grab the type of the input arguments
                ctrl_copy.type_context[const_param.p4_type] = args[idx].sort()
        return ctrl_copy

    def __call__(self, *args, **kwargs):
        raise RuntimeError("P4Controls are not directly callable!")

    def apply(self, p4_state, *args, **kwargs):
        local_context = {}
        for type_name, p4_type in self.type_context.items():
            local_context[type_name] = resolve_type(p4_state, p4_type)
        p4_state.type_contexts.append(self.type_context)
        self.eval(p4_state, *args, **kwargs)
        p4_state.type_contexts.pop()

    def eval_callable(self, p4_state, merged_args, var_buffer):
        # initialize the local context of the function for execution
        context = p4_state.current_context()

        merged_vars = save_variables(p4_state, self.merged_consts)
        context.prepend_to_buffer(merged_vars)

        for const_param_name, const_arg in self.merged_consts.items():
            const_val = const_arg.p4_val
            const_val = p4_state.resolve_expr(const_val)
            p4_state.set_or_add_var(const_param_name, const_val)
        for expr in self.local_decls:
            expr.eval(p4_state)
            if p4_state.has_exited or context.has_returned:
                break
        self.statements.eval(p4_state)

    def __copy__(self):
        cls = self.__class__
        result = cls.__new__(cls)
        result.__dict__.update(self.__dict__)
        result.type_params = copy.copy(self.type_params)
        result.params = []
        for param in self.params:
            result.params.append(copy.copy(param))
        result.const_params = []
        for param in self.const_params:
            result.const_params.append(copy.copy(param))
        result.locals = {}
        result.locals["apply"] = result.apply
        return result


class P4Method(P4Callable):

    def __init__(self, name, type_params, params):
        super(P4Method, self).__init__(name, params)
        # P4Methods, which are also black-box functions, can have return types
        self.return_type = type_params[0]
        self.type_params = type_params[1]
        self.type_context = {}
        self.extern_context = {}

    def copy_in(self, p4_state, merged_args):
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
            p4_type = resolve_type(p4_state, arg.p4_type)
            if isinstance(arg_expr, list):
                # if the type is undefined, do nothing
                if isinstance(p4_type, P4ComplexType):
                    arg_instance = gen_instance(
                        p4_state, arg_name, p4_type)
                    arg_instance.set_list(arg_expr)
                    arg_expr = arg_instance
                else:
                    # synthesize a list type from the input list
                    # this mostly just a dummy
                    # FIXME: Need to get the actual types
                    p4_type = ListType("tuple", p4_state, arg_expr)
            # FIXME Check this hack. This is type inference based on arguments
            if p4_type is None:
                self.type_context[arg.p4_type] = arg_expr.sort()
            # it is possible to pass an int as value, we need to cast it
            if isinstance(arg_expr, int):
                arg_expr = z3_cast(arg_expr, p4_type)
            if arg.is_ref in ("inout", "out"):
                # outs are left-values so the arg must be a string
                # infer the type value at runtime, param does not work yet
                # outs reset the input
                # In the case that the instance is a complex type make sure
                # to propagate the variable through all its members
                arg_expr = gen_instance(p4_state, arg_name, arg_expr.sort())
                if isinstance(arg_expr, P4ComplexInstance):
                    # we do not know whether the expression is valid afterwards
                    propagate_validity_bit(arg_expr)
            # buffer the value, do NOT set it yet
            param_buffer[param_name] = arg_expr
        return param_buffer

    def __call__(self, p4_state, *args, **kwargs):
        local_context = {}
        for type_name, p4_type in self.extern_context.items():
            local_context[type_name] = resolve_type(p4_state, p4_type)
        p4_state.type_contexts.append(local_context)
        expr = self.eval(p4_state, *args, **kwargs)
        p4_state.type_contexts.pop()
        return expr

    def __copy__(self):
        cls = self.__class__
        result = cls.__new__(cls)
        result.__dict__.update(self.__dict__)
        result.type_params = copy.copy(self.type_params)
        result.params = []
        for param in self.params:
            result.params.append(copy.copy(param))
        return result

    def init_type_params(self, *args, **kwargs):
        # TODO Figure out what to actually do here
        init_ctrl = copy.copy(self)
        # the type params sometimes include the return type also
        # it is typically the first value, but is bound somewhere else
        for idx, t_param in enumerate(init_ctrl.type_params):
            init_ctrl.type_context[t_param] = args[idx]
            for param in init_ctrl.params:
                if isinstance(param.p4_type, str) and param.p4_type == t_param:
                    param.p4_type = args[idx]
        return init_ctrl

    def initialize(self, context, *args, **kwargs):
        # # TODO Figure out what to actually do here
        init_method = copy.copy(self)
        # # deepcopy is important to ensure independent type inference
        # # the type params sometimes include the return type also
        # # it is typically the first value, but is bound somewhere else
        # if len(args) < len(init_method.type_params):
        #     type_list = init_method.type_params[1:]
        # else:
        #     type_list = init_method.type_params
        # for idx, t_param in enumerate(type_list):
        #     if init_method.return_type == t_param:
        #         init_method.return_type = args[idx]
        #     for method_param in init_method.params:
        #         if method_param.p4_type == t_param:
        #             method_param.p4_type = args[idx]
        return init_method

    def eval_callable(self, p4_state, merged_args, var_buffer):
        local_context = {}
        for type_name, p4_type in self.type_context.items():
            local_context[type_name] = resolve_type(p4_state, p4_type)
        p4_state.type_contexts.append(local_context)
        # initialize the local context of the function for execution
        if self.return_type is None:
            return None
        # methods can return values, we need to generate a new constant
        # we generate the name based on the input arguments
        # var_name = ""
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
        return_instance = gen_instance(p4_state, self.name, self.return_type)
        # a returned header may or may not be valid
        if isinstance(return_instance, P4ComplexInstance):
            propagate_validity_bit(return_instance)
        p4_state.type_contexts.pop()
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
        super(P4Table, self).__init__(name, params={})
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

    def eval_action(self, p4_state, action_name, action_args):
        p4_action = p4_state.resolve_reference(action_name)
        if not isinstance(p4_action, P4Action):
            raise TypeError(f"Expected a P4Action got {type(p4_action)}!")
        merged_action_args = []
        action_args_len = len(action_args) - 1
        for idx, param in enumerate(p4_action.params):
            if idx > action_args_len:
                # this is a ctrl argument, generate an input
                ctrl_arg = gen_instance(p4_state,
                                        f"{self.name}{param.name}", param.p4_type)
                merged_action_args.append(ctrl_arg)
            else:
                merged_action_args.append(action_args[idx])
        return p4_action(p4_state, *merged_action_args)

    def eval_default(self, p4_state):
        _, action_name, action_args = self.default_action
        log.debug("Evaluating default action...")
        return self.eval_action(p4_state, action_name, action_args)

    def eval_const_entries(self, p4_state, action_exprs, action_matches):
        context = p4_state.current_context()
        forward_cond_copy = context.tmp_forward_cond
        for c_keys, (action_name, action_args) in reversed(self.const_entries):
            matches = []
            # match the constant keys with the normal table keys
            # this generates the match expression for a specific constant entry
            # this is a little inefficient, fix.
            for index, key in enumerate(self.keys):
                c_key_expr = c_keys[index]
                # default implies don't care, do not add
                # TODO: Verify that this assumption is right...
                if isinstance(c_key_expr, DefaultExpression):
                    continue
                key_eval = p4_state.resolve_expr(key)
                if isinstance(c_key_expr, P4Range):
                    x = c_key_expr.min
                    y = c_key_expr.max
                    const_name = f"{self.name}_range_{index}"
                    range_const = z3.Const(const_name, key_eval.sort())
                    c_key_eval = z3.If(range_const <= x, x, z3.If(
                        range_const >= y, y, range_const))
                else:
                    c_key_eval = p4_state.resolve_expr(c_key_expr)

                matches.append(key_eval == c_key_eval)
            action_match = z3.And(*matches)
            log.debug("Evaluating constant action %s...", action_name)
            # state forks here
            var_store, contexts = p4_state.checkpoint()
            cond = z3.And(self.locals["hit"], action_match)
            context.tmp_forward_cond = z3.And(forward_cond_copy, cond)
            self.eval_action(p4_state, action_name, action_args)
            if not p4_state.has_exited:
                action_exprs.append((cond, p4_state.get_attrs()))
            p4_state.has_exited = False
            action_matches.append(action_match)
            p4_state.restore(var_store, contexts)

    def eval_table_entries(self, p4_state, action_exprs, action_matches):
        context = p4_state.current_context()
        forward_cond_copy = context.tmp_forward_cond
        for act_id, act_name, act_args in reversed(self.actions.values()):
            action_match = (self.tbl_action == z3.IntVal(act_id))
            log.debug("Evaluating action %s...", act_name)
            # state forks here
            var_store, contexts = p4_state.checkpoint()
            cond = z3.And(self.locals["hit"], action_match)
            context.tmp_forward_cond = z3.And(forward_cond_copy, cond)
            self.eval_action(p4_state, act_name, act_args)
            if not p4_state.has_exited:
                action_exprs.append((cond, p4_state.get_attrs()))
            p4_state.has_exited = False
            action_matches.append(action_match)
            p4_state.restore(var_store, contexts)

    def eval_table(self, p4_state):
        action_exprs = []
        action_matches = []
        context = p4_state.current_context()
        forward_cond_copy = context.tmp_forward_cond

        # only bother to evaluate if the table can actually hit
        if not self.locals["hit"] == z3.BoolVal(False):
            # note: the action lists are pass by reference here
            # first evaluate all the constant entries
            self.eval_const_entries(p4_state, action_exprs, action_matches)
            # then append dynamic table entries to the constant entries
            self.eval_table_entries(p4_state, action_exprs, action_matches)
        # finally start evaluating the default entry
        var_store, contexts = p4_state.checkpoint()
        # this hits when the table is either missed, or no action matches
        cond = z3.Or(self.locals["miss"], z3.Not(z3.Or(*action_matches)))
        context.tmp_forward_cond = z3.And(forward_cond_copy, cond)
        self.eval_default(p4_state)
        if p4_state.has_exited:
            p4_state.restore(var_store, contexts)
        p4_state.has_exited = False
        context.tmp_forward_cond = forward_cond_copy
        # generate a nested set of if expressions per available action
        for cond, then_vars in action_exprs:
            merge_attrs(p4_state, cond, then_vars)

    def eval_callable(self, p4_state, merged_args, var_buffer):
        # tables are a little bit special since they also have attributes
        # so what we do here is first initialize the key
        hit = self.eval_keys(p4_state)
        self.locals["hit"] = z3.simplify(hit)
        self.locals["miss"] = z3.Not(hit)
        # then execute the table as the next expression in the chain
        self.eval_table(p4_state)
