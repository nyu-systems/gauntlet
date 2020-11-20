from collections import OrderedDict
from p4z3.base import z3, log, copy, resolve_type, gen_instance
from p4z3.base import P4ComplexType, P4Member, P4Extern, propagate_validity_bit
from p4z3.state import P4Context, P4State
from p4z3.callables import P4Callable, P4Control, merge_parameters


class P4Package(P4Callable):

    def __init__(self, name, params, type_params):
        super(P4Package, self).__init__(name, params)
        self.pipes = OrderedDict()
        self.type_params = type_params
        self.type_context = {}

    def init_type_params(self, context, *args, **kwargs):
        init_package = copy.copy(self)
        for idx, t_param in enumerate(init_package.type_params):
            arg = resolve_type(context, args[idx])
            init_package.type_context[t_param] = arg
        return init_package

    def create_z3_representation(self, p4_state, context):
        members = p4_state.get_members(context)
        # and also merge back all the exit states we collected
        for exit_cond, exit_state in reversed(context.get_exit_states()):
            for idx, exit_member in enumerate(exit_state):
                members[idx] = z3.If(exit_cond, exit_member, members[idx])
        return p4_state.z3_type.constructor(0)(*members)

    def create_p4_state(self, ctx, name, z3_args, instances):
        p4_state = P4State([])
        p4_state.name = name
        p4_state.members = z3_args

        for instance_name, instance_val in instances.items():
            ctx.set_or_add_var(instance_name, instance_val)

        flat_args = []
        idx = 0
        for z3_arg_name, z3_arg_type in z3_args:
            z3_arg_type = resolve_type(p4_state, z3_arg_type)
            if isinstance(z3_arg_type, P4ComplexType):
                member_cls = z3_arg_type.instantiate(f"{name}.{idx}")
                propagate_validity_bit(member_cls)
                for sub_member in z3_arg_type.flat_names:
                    flat_args.append((str(idx), sub_member.p4_type))
                    p4_state.flat_names.append(
                        P4Member(z3_arg_name, sub_member.name))
                    idx += 1
                # this is a complex datatype, create a P4ComplexType
                ctx.set_or_add_var(z3_arg_name, member_cls, True)
            else:
                flat_args.append((str(idx), z3_arg_type))
                p4_state.flat_names.append(z3_arg_name)
                idx += 1
        z3_type = z3.Datatype(name)
        z3_type.declare(f"mk_{name}", *flat_args)
        p4_state.z3_type = z3_type.create()
        p4_state.const = z3.Const(name, p4_state.z3_type)

        for type_idx, arg_name in enumerate(p4_state.flat_names):
            member_constructor = p4_state.z3_type.accessor(0, type_idx)
            ctx.set_or_add_var(
                arg_name, member_constructor(p4_state.const), True)
        return p4_state

    def init_state(self, ctx, type_ctx, name, p4_params):
        stripped_args = []
        instances = {}
        # for extern_set in p4_state.extern_extensions:
        #     for extern_name, extern in extern_set.items():
        #         ctx.add_type(extern_name, extern)
        for param in p4_params:
            p4_type = resolve_type(type_ctx, param.p4_type)
            if param.mode in ("inout", "out"):
                # only inouts or outs matter as output
                stripped_args.append((param.name, p4_type))
            else:
                # for other inputs we can instantiate something
                instance = gen_instance(type_ctx, param.name, p4_type)
                instances[param.name] = instance
        return self.create_p4_state(ctx, name, stripped_args, instances)

    def type_inference(self, context, pipe_val, pipe_arg):
        pass
    def compute_args(self, context, pipe_val, pipe_arg):
        pass

    def initialize(self, context, *args, **kwargs):
        merged_args = merge_parameters(self.params, *args, **kwargs)
        for pipe_name, pipe_arg in merged_args.items():
            if pipe_arg.p4_val is None:
                # for some reason, the argument is uninitialized.
                # FIXME: This should not happen. Why?
                continue
            log.info("Loading %s pipe...", pipe_name)
            pipe_val = context.resolve_expr(pipe_arg.p4_val)
            if isinstance(pipe_val, P4Control):
                # create the z3 representation of this control state
                type_ctx = P4Context(context, {})
                # This boilerplate is all necessary to initialize state...
                # FIXME: Ideally, this should be handled by the control...
                for type_name, p4_type in self.type_context.items():
                    type_ctx.add_type(type_name, p4_type)
                ctrl_type = resolve_type(type_ctx, pipe_arg.p4_type)
                pipe_val = pipe_val.bind_to_ctrl_type(type_ctx, ctrl_type)
                for type_name, p4_type in ctrl_type.type_context.items():
                    type_ctx.add_type(
                        type_name, resolve_type(type_ctx, p4_type))
                args = []
                ctrl_type = resolve_type(type_ctx, pipe_arg.p4_type)
                for idx, param in enumerate(pipe_val.params):
                    ctrl_type_param_type = ctrl_type.params[idx].p4_type
                    generic_type = resolve_type(type_ctx, ctrl_type_param_type)
                    if generic_type is None:
                        param_type = resolve_type(type_ctx, param.p4_type)
                        self.type_context[ctrl_type_param_type] = param_type
                    args.append(param.name)
                ctx = P4Context(context, {})
                p4_state = self.init_state(ctx, type_ctx, pipe_name, pipe_val.params)
                ctx.set_p4_state(p4_state)
                # initialize the call with its own params we collected
                # this is essentially the input packet
                pipe_val.apply(ctx, *args)
                # after executing the pipeline get its z3 representation
                z3_function = self.create_z3_representation(p4_state, ctx)
                # all done, that is our P4 representation!
                self.pipes[pipe_name] = (
                    z3_function, p4_state.members, pipe_val)
            elif isinstance(pipe_val, P4Extern):
                var = z3.Const(f"{pipe_name}{pipe_val.name}", pipe_val.z3_type)
                self.pipes[pipe_name] = (var, [], pipe_val)
            elif isinstance(pipe_val, P4Package):
                # execute the package by calling its initializer
                pipe_val.initialize(context)
                # resolve all the sub_pipes
                for sub_pipe_name, sub_pipe_val in pipe_val.pipes.items():
                    sub_pipe_name = f"{pipe_name}_{sub_pipe_name}"
                    self.pipes[sub_pipe_name] = sub_pipe_val
            elif isinstance(pipe_val, z3.ExprRef):
                # for some reason simple expressions are also possible.
                self.pipes[pipe_name] = (pipe_val, [], pipe_val)
            else:
                raise RuntimeError(
                    f"Unsupported value {pipe_val}, type {type(pipe_val)}."
                    " It does not make sense as a P4 pipeline.")
        return self

    def get_pipes(self):
        return self.pipes
