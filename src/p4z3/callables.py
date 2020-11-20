from collections import OrderedDict
from p4z3.state import P4Context
from p4z3.base import z3, log, copy, merge_attrs
from p4z3.base import gen_instance, z3_cast, handle_mux, StructInstance
from p4z3.base import P4Z3Class, P4Mask, P4ComplexType, UNDEF_LABEL
from p4z3.base import DefaultExpression, propagate_validity_bit
from p4z3.base import P4Expression, P4Argument, P4Range, resolve_type, ListType


def save_variables(context, merged_args):
    var_buffer = OrderedDict()
    # save all the variables that may be overridden
    for param_name, arg in merged_args.items():
        try:
            param_val = context.resolve_reference(param_name)
            var_buffer[param_name] = (arg.mode, arg.p4_val, param_val)
        except RuntimeError:
            # if the variable name does not exist, set the value to None
            var_buffer[param_name] = (arg.mode, arg.p4_val, None)
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
            arg = P4Argument(param.mode, param.p4_type, arg_val)
        elif param.p4_default is not None:
            # there is no argument but we have a default value, so use that
            arg_val = param.p4_default
            arg = P4Argument(param.mode, param.p4_type, arg_val)
        else:
            # sometimes we get optional parameters, record the name and type
            arg = P4Argument(param.mode, param.p4_type, None)
        merged_args[param.name] = arg
    for param_name, arg_val in kwargs.items():
        # this is expensive but at least works reliably
        if isinstance(arg_val, DefaultExpression):
            # Default expressions are pointless arguments, so skip them
            continue
        for param in params:
            if param.name == param_name:
                arg = P4Argument(param.mode, param.p4_type, arg_val)
                merged_args[param_name] = arg
    return merged_args


class MethodCallExpr(P4Expression):

    def __init__(self, p4_method, type_args, *args, **kwargs):
        self.p4_method = p4_method
        self.args = args
        self.kwargs = kwargs
        self.type_args = type_args

    def pick_method(self, method_list):
        arg_len = len(self.args) + len(self.kwargs)
        for method in method_list:
            if len(method.params) == arg_len:
                return method
        # do not really know how to match, use the last declaration
        # this happens because of default values, no idea how to resolve yet
        return method_list[-1]

    def eval(self, context):
        p4_method = self.p4_method
        # if we get a reference just try to find the method in the state
        if not callable(p4_method):
            p4_method = context.resolve_expr(p4_method)
        # methods may be overloaded
        # we use a dumb method where we match the number of parameters
        if isinstance(p4_method, list):
            p4_method = self.pick_method(p4_method)
        # Method calls might sometimes have type arguments
        # bind the method
        if isinstance(p4_method, P4Method) and self.type_args:
            p4_method = p4_method.init_type_params(context, *self.type_args)
        return p4_method(context, *self.args, **self.kwargs)


class P4Callable(P4Z3Class):
    def __init__(self, name, params, body=[]):
        self.name = name
        self.statements = body
        self.params = params
        self.call_counter = 0
        self.locals = {}

    def eval_callable(self, context, merged_args, var_buffer):
        raise NotImplementedError("Method eval_callable not implemented!")

    def eval(self, context, *args, **kwargs):
        merged_args = merge_parameters(self.params, *args, **kwargs)
        var_buffer = save_variables(context, merged_args)
        param_buffer = self.copy_in(context, merged_args)
        # only add the context after all the arguments have been resolved
        sub_ctx = P4Context(context, var_buffer)
        # now we can set the arguments without influencing subsequent variables
        for param_name, param_val in param_buffer.items():
            sub_ctx.set_or_add_var(param_name, param_val)

        # execute the action expression with the new environment
        expr = self.eval_callable(sub_ctx, merged_args, var_buffer)
        self.call_counter += 1

        while sub_ctx.return_states:
            cond, return_attrs = sub_ctx.return_states.pop()
            merge_attrs(sub_ctx, cond, return_attrs)
        sub_ctx.copy_out(context)
        return expr

    def __call__(self, context, *args, **kwargs):
        raise NotImplementedError("Method __call__ not implemented!")

    def copy_in(self, context, merged_args):
        param_buffer = OrderedDict()
        for param_name, arg in merged_args.items():
            # Sometimes expressions are passed, resolve those first
            arg_expr = context.resolve_expr(arg.p4_val)
            # it can happen that we receive a list
            # infer the type, generate, and set
            p4_type = resolve_type(context, arg.p4_type)
            if isinstance(arg_expr, list):
                # if the type is undefined, do nothing
                if isinstance(p4_type, P4ComplexType):
                    arg_instance = gen_instance(context, UNDEF_LABEL, p4_type)
                    arg_instance.set_list(arg_expr)
                    arg_expr = arg_instance
            # it is possible to pass an int as value, we need to cast it
            elif isinstance(arg_expr, int):
                arg_expr = z3_cast(arg_expr, p4_type)
            # need to work with an independent copy
            # the purpose is to handle indirect assignments in an action
            if arg.mode in ("in", "inout") and isinstance(arg_expr, StructInstance):
                arg_expr = copy.copy(arg_expr)
            if arg.mode == "out":
                # outs are left-values so the arg must be a string
                # infer the type value at runtime, param does not work yet
                # outs reset the input
                # In the case that the instance is a complex type make sure
                # to propagate the variable through all its members
                log.debug("Resetting %s to %s", arg_expr, param_name)
                arg_expr = gen_instance(context, UNDEF_LABEL, p4_type)

            log.debug("Copy-in: %s to %s", arg_expr, param_name)
            # buffer the value, do NOT set it yet
            param_buffer[param_name] = arg_expr
        return param_buffer

    def resolve_reference(self, var):
        return self.locals[var]


class ConstCallExpr(P4Expression):

    def __init__(self, p4_method, *args, **kwargs):
        self.p4_method = p4_method
        self.args = args
        self.kwargs = kwargs

    def eval(self, context):
        p4_method = resolve_type(context, self.p4_method)
        return p4_method.initialize(context, *self.args, **self.kwargs)



class P4Action(P4Callable):

    def eval_callable(self, context, merged_args, var_buffer):
        # actions can modify global variables so do not save the p4 state
        # the only variables that do need to be restored are copy-ins/outs
        self.statements.eval(context)

    def __call__(self, context, *args, **kwargs):
        return self.eval(context, *args, **kwargs)

class P4Function(P4Action):

    def __init__(self, name, params, return_type, body):
        super(P4Function, self).__init__(name, params, body)
        self.return_type = return_type

    def eval_callable(self, context, merged_args, var_buffer):
        # execute the action expression with the new environment
        context.return_type = self.return_type
        self.statements.eval(context)
        return_expr = None
        if len(context.return_exprs) == 1:
            _, return_expr = context.return_exprs.pop()
        elif len(context.return_exprs) > 1:
            # the first condition is not needed since it is the default
            _, return_expr = context.return_exprs.pop()
            if isinstance(return_expr, StructInstance):
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

    def bind_to_ctrl_type(self, context, ctrl_type):
        # TODO Figure out what to actually do here
        # FIXME: A hack to deal with lack of input params
        if len(ctrl_type.params) < len(self.type_params):
            return self
        init_ctrl = copy.copy(self)
        # the type params sometimes include the return type also
        # it is typically the first value, but is bound somewhere else
        for idx, t_param in enumerate(init_ctrl.type_params):
            sub_type = resolve_type(context, ctrl_type.params[idx].p4_type)
            init_ctrl.type_context[t_param] = sub_type
            for param_idx, param in enumerate(init_ctrl.params):
                if isinstance(param.p4_type, str) and param.p4_type == t_param:
                    init_ctrl.params[param_idx] = ctrl_type.params[idx]
        return init_ctrl

    def init_type_params(self, context, *args, **kwargs):
        # TODO Figure out what to actually do here
        init_ctrl = copy.copy(self)
        # the type params sometimes include the return type also
        # it is typically the first value, but is bound somewhere else
        for idx, t_param in enumerate(init_ctrl.type_params):
            arg = resolve_type(context, args[idx])
            init_ctrl.type_context[t_param] = arg
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

    def apply(self, context, *args, **kwargs):
        for type_name, p4_type in self.type_context.items():
            context.add_type(type_name, resolve_type(context, p4_type))
        self.eval(context, *args, **kwargs)

    def eval_callable(self, context, merged_args, var_buffer):
        # initialize the local context of the function for execution

        merged_vars = save_variables(context, self.merged_consts)
        context.prepend_to_buffer(merged_vars)

        for const_param_name, const_arg in self.merged_consts.items():
            const_val = const_arg.p4_val
            const_val = context.resolve_expr(const_val)
            context.set_or_add_var(const_param_name, const_val)
        for expr in self.local_decls:
            expr.eval(context)
            if context.get_exited() or context.has_returned:
                break
        self.statements.eval(context)

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

    def assign_values(self, context, method_args):
        for param_name, arg in method_args.items():
            arg_mode, arg_ref, arg_expr, p4_src_type = arg
            # infer the type
            p4_type = resolve_type(context, p4_src_type)
            # This is dynamic type inference based on arguments
            # FIXME Check this hack.
            if p4_type is None:
                if isinstance(arg_expr, list):
                    # synthesize a list type from the input list
                    # this mostly just a dummy
                    # FIXME: Need to get the actual sub-types
                    p4_type = ListType("tuple", context, arg_expr)
                else:
                    p4_type = arg_expr.sort()
                context.add_type(p4_src_type, p4_type)

            if arg_mode not in ("out", "inout"):
                # this value is read-only so we do not care
                # however, we still used it to potentially infer a type
                continue

            arg_name = f"{self.name}_{param_name}"
            arg_expr = gen_instance(context, arg_name, p4_type)

            if isinstance(arg_expr, StructInstance):
                # # In the case that the instance is a complex type make sure
                # # to propagate the variable through all its members
                # bind_const = z3.Const(arg_name, arg_expr.z3_type)
                # arg_expr.bind(bind_const)
                # we do not know whether the expression is valid afterwards
                propagate_validity_bit(arg_expr)
            # (in)outs are left-values so the arg_ref must be a string
            context.set_or_add_var(arg_ref, arg_expr)

    def __call__(self, context, *args, **kwargs):
        merged_args = merge_parameters(self.params, *args, **kwargs)
        sub_ctx = P4Context(context, {})
        # resolve the inputs *before* we bind types
        method_args = {}
        for param_name, arg in merged_args.items():
            # we need to resolve "in" too because of side-effects
            if arg.p4_val is None:
                # sometimes we get optional parameters
                # FIXME: I do not actually know how to resolve them right now
                arg_expr = gen_instance(sub_ctx, "optional", arg.p4_type)
            else:
                arg_expr = sub_ctx.resolve_expr(arg.p4_val)
            method_args[param_name] = (
                arg.mode, arg.p4_val, arg_expr, arg.p4_type)

        # apply the local and parent extern type contexts
        for type_name, p4_type in self.extern_context.items():
            sub_ctx.add_type(type_name, resolve_type(sub_ctx, p4_type))
        for type_name, p4_type in self.type_context.items():
            sub_ctx.add_type(type_name, resolve_type(sub_ctx, p4_type))

        # assign symbolic values to the inputs that are inout and out
        self.assign_values(sub_ctx, method_args)

        # execute the return expression within the new type environment
        expr = self.eval_callable(sub_ctx, merged_args, {})
        self.call_counter += 1
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

    def init_type_params(self, context, *args, **kwargs):
        init_method = copy.copy(self)
        for idx, t_param in enumerate(init_method.type_params):
            arg = resolve_type(context, args[idx])
            init_method.type_context[t_param] = arg
        return init_method

    def eval_callable(self, context, merged_args, var_buffer):
        # initialize the local context of the function for execution
        if self.return_type is None:
            return None
        # methods can return values, we need to generate a new constant
        # we generate the name based on the input arguments
        # var_name = ""
        # for arg in merged_args.values():
        #     arg = context.resolve_expr(arg.p4_val)
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
        return_instance = gen_instance(context, self.name, self.return_type)
        # a returned header may or may not be valid
        if isinstance(return_instance, StructInstance):
            propagate_validity_bit(return_instance)
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
        self.implementation = None
        self.locals["hit"] = z3.BoolVal(False)
        self.locals["miss"] = z3.BoolVal(True)
        self.locals["action_run"] = self
        self.locals["apply"] = self.apply

        # some custom logic to resolve properties
        self.add_keys(properties)
        self.add_default(properties)
        self.add_actions(properties)
        self.add_const_entries(properties)

        # check if the table is immutable
        self.immutable = properties["immutable"]

        # set the rest
        self.properties = properties

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

    def apply(self, context):
        self.eval(context)
        return self

    def eval_keys(self, context):
        key_pairs = []
        if not self.keys:
            # there is nothing to match with...
            return z3.BoolVal(False)
        for index, (key_expr, key_type) in enumerate(self.keys):
            key_eval = context.resolve_expr(key_expr)
            key_sort = key_eval.sort()
            key_match = z3.Const(f"{self.name}_table_key_{index}", key_sort)
            if key_type == "exact":
                # Just a simple comparison, nothing special
                key_pairs.append(key_eval == key_match)
            elif key_type == "lpm":
                # I think this can be arbitrarily large...
                # If the shift exceeds the bit width, everything will be zero
                # but that does not matter
                # TODO: Test this?
                mask_var = z3.BitVec(
                    f"{self.name}_table_mask_{index}", key_sort)
                lpm_mask = z3.BitVecVal(
                    2**key_sort.size() - 1, key_sort) << mask_var
                match = (key_eval & lpm_mask) == (key_match & lpm_mask)
                key_pairs.append(match)
            elif key_type == "ternary":
                # Just apply a symbolic mask, any zero bit is a wildcard
                # TODO: Test this?
                mask = z3.Const(f"{self.name}_table_mask_{index}", key_sort)
                # this is dumb...
                if isinstance(key_sort, z3.BoolSortRef):
                    match = z3.And(key_eval, mask) == z3.And(key_match, mask)
                else:
                    match = (key_eval & mask) == (key_match & mask)
                key_pairs.append(match)
            elif key_type == "range":
                # Pick an arbitrary minimum and maximum within the bit range
                # the minimum must be strictly lesser than the max
                # I do not think a match is needed?
                # TODO: Test this?
                min_key = z3.Const(f"{self.name}_table_min_{index}", key_sort)
                max_key = z3.Const(f"{self.name}_table_max_{index}", key_sort)
                match = z3.And(z3.ULE(min_key, key_eval),
                               z3.UGE(max_key, key_eval))
                key_pairs.append(z3.And(match, z3.ULT(min_key, max_key)))
            elif key_type == "optional":
                # As far as I understand this is just a wildcard for control
                # plane purposes. Semantically, there is no point?
                # TODO: Test this?
                key_pairs.append(z3.BoolVal(True))
            elif key_type == "selector":
                # Selectors are a deep rabbit hole
                # This rabbit hole does not yet make sense to me
                # FIXME: Implement
                # will intentionally fail if no implementation is present
                # impl = self.properties["implementation"]
                # impl_extern = self.prog_state.resolve_reference(impl)
                key_pairs.append(z3.BoolVal(True))
            else:
                # weird key, might be some specific specification
                raise RuntimeError(f"Key type {key_type} not supported!")
        return z3.And(key_pairs)

    def eval_action(self, context, action_name, action_args):
        p4_action = context.resolve_reference(action_name)
        if not isinstance(p4_action, P4Action):
            raise TypeError(f"Expected a P4Action got {type(p4_action)}!")
        merged_action_args = []
        action_args_len = len(action_args) - 1
        for idx, param in enumerate(p4_action.params):
            if idx > action_args_len:
                # this is a ctrl argument, generate an input
                ctrl_arg = gen_instance(context, f"{self.name}{param.name}",
                                        param.p4_type)
                merged_action_args.append(ctrl_arg)
            else:
                merged_action_args.append(action_args[idx])
        return p4_action(context, *merged_action_args)

    def eval_default(self, context):
        _, action_name, action_args = self.default_action
        log.debug("Evaluating default action...")
        return self.eval_action(context, action_name, action_args)

    def get_const_matches(self, context, c_keys):
        matches = []
        # match the constant keys with the normal table keys
        # this generates the match expression for a specific constant entry
        # this is a little inefficient, FIXME.
        for index, (key_expr, _) in enumerate(self.keys):
            c_key_expr = c_keys[index]
            # default implies don't care, do not add
            # TODO: Verify that this assumption is right...
            if isinstance(c_key_expr, DefaultExpression):
                continue
            # TODO: Unclear about the role of side-effects here
            key_eval = context.resolve_expr(key_expr)
            if isinstance(c_key_expr, P4Range):
                x = context.resolve_expr(c_key_expr.min)
                y = context.resolve_expr(c_key_expr.max)
                c_key_eval = z3.And(z3.ULE(x, key_eval),
                                    z3.UGE(y, key_eval))
                matches.append(c_key_eval)
            elif isinstance(c_key_expr, P4Mask):
                # TODO: Unclear about the role of side-effects here
                val = context.resolve_expr(c_key_expr.value)
                mask = context.resolve_expr(c_key_expr.mask)
                c_key_eval = (val & mask) == (key_eval & mask)
                matches.append(c_key_eval)
            else:
                c_key_eval = context.resolve_expr(c_key_expr)
                matches.append(key_eval == c_key_eval)
        return z3.And(*matches)

    def eval_const_entries(self, context, action_exprs, action_matches):
        forward_cond_copy = context.tmp_forward_cond
        for c_keys, (action_name, action_args) in reversed(self.const_entries):

            action_match = self.get_const_matches(context, c_keys)
            log.debug("Evaluating constant action %s...", action_name)
            # state forks here
            var_store, contexts = context.checkpoint()
            cond = z3.And(self.locals["hit"], action_match)
            context.tmp_forward_cond = z3.And(forward_cond_copy, cond)
            self.eval_action(context, action_name, action_args)
            if not context.get_exited():
                action_exprs.append((cond, context.get_attrs()))
            context.set_exited(False)
            action_matches.append(action_match)
            context.restore(var_store, contexts)

    def eval_table_entries(self, context, action_exprs, action_matches):
        forward_cond_copy = context.tmp_forward_cond
        for act_id, act_name, act_args in reversed(self.actions.values()):
            action_match = (self.tbl_action == z3.IntVal(act_id))
            log.debug("Evaluating action %s...", act_name)
            # state forks here
            var_store, contexts = context.checkpoint()
            cond = z3.And(self.locals["hit"], action_match)
            context.tmp_forward_cond = z3.And(forward_cond_copy, cond)
            self.eval_action(context, act_name, act_args)
            if not context.get_exited():
                action_exprs.append((cond, context.get_attrs()))
            context.set_exited(False)
            action_matches.append(action_match)
            context.restore(var_store, contexts)

    def eval_table(self, context):
        action_exprs = []
        action_matches = []
        forward_cond_copy = context.tmp_forward_cond

        # only bother to evaluate if the table can actually hit
        if not z3.is_false(self.locals["hit"]):
            # note: the action lists are pass by reference here
            # first evaluate all the constant entries
            self.eval_const_entries(context, action_exprs, action_matches)
            # then append dynamic table entries to the constant entries
            # only do this if the table can actually be manipulated
            if not self.immutable:
                self.eval_table_entries(context, action_exprs, action_matches)
        # finally start evaluating the default entry
        var_store, contexts = context.checkpoint()
        # this hits when the table is either missed, or no action matches
        cond = z3.Or(self.locals["miss"], z3.Not(z3.Or(*action_matches)))
        context.tmp_forward_cond = z3.And(forward_cond_copy, cond)
        self.eval_default(context)
        if context.get_exited():
            context.restore(var_store, contexts)
        context.set_exited(False)
        context.tmp_forward_cond = forward_cond_copy
        # generate a nested set of if expressions per available action
        for cond, then_vars in action_exprs:
            merge_attrs(context, cond, then_vars)

    def eval_callable(self, context, merged_args, var_buffer):
        # tables are a little bit special since they also have attributes
        # so what we do here is first initialize the key
        hit = self.eval_keys(context)
        self.locals["hit"] = z3.simplify(hit)
        self.locals["miss"] = z3.Not(hit)
        # then execute the table as the next expression in the chain
        self.eval_table(context)
