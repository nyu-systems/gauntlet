from collections import OrderedDict
from p4z3.base import z3, log, copy
from p4z3.base import P4Extern, StaticType
from p4z3.state import LocalContext, P4State
from p4z3.callables import P4Control, merge_parameters


def create_state_args(state_ctx, type_ctx, p4_params):
    state_args = []
    instances = {}
    for param in p4_params:
        p4_type = type_ctx.resolve_type(param.p4_type)
        if param.mode in ("inout", "out"):
            # only inouts or outs matter as output
            state_args.append((param.name, p4_type))
        else:
            # for other inputs we can instantiate something
            instance = type_ctx.gen_instance(param.name, p4_type)
            instances[param.name] = instance
            state_ctx.set_or_add_var(param.name, instance)
    return state_args

class P4Package(StaticType):

    def __init__(self, name, params, type_params):
        super(P4Package, self).__init__()
        self.pipes = OrderedDict()
        self.name = name
        self.params = params
        self.type_params = type_params
        self.type_ctx = {}

    def init_type_params(self, _ctx, *args, **kwargs):
        init_package = copy.copy(self)
        for idx, t_param in enumerate(init_package.type_params):
            init_package.type_ctx[t_param] = args[idx]
        return init_package

    def type_inference(self, type_ctx, pipe_val, pipe_arg):
        # This boilerplate is all necessary to initialize state...
        # FIXME: Ideally, this should be handled by the control...
        for type_name, p4_type in self.type_ctx.items():
            type_ctx.add_type(type_name, type_ctx.resolve_type(p4_type))
        ctrl_type = type_ctx.resolve_type(pipe_arg.p4_type)
        for type_name, p4_type in ctrl_type.type_ctx.items():
            try:
                type_ctx.add_type(type_name, type_ctx.resolve_type(p4_type))
            except KeyError:
                pass
        for idx, param in enumerate(pipe_val.params):
            ctrl_type_par_type = ctrl_type.params[idx].p4_type
            try:
                type_ctx.resolve_type(ctrl_type_par_type)
            except KeyError:
                par_type = type_ctx.resolve_type(param.p4_type)
                type_ctx.add_type(ctrl_type_par_type, par_type)
                self.type_ctx[ctrl_type_par_type] = par_type
        pipe_val = pipe_val.bind_to_ctrl_type(type_ctx, ctrl_type)
        return pipe_val

    def build_state_ctx(self, main_ctx, pipe_name, pipe_arg, pipe_val):
        type_ctx = LocalContext(main_ctx, {})
        pipe_val = self.type_inference(type_ctx, pipe_val, pipe_arg)
        state_ctx = LocalContext(main_ctx, {})
        for extern_name, extern in main_ctx.get_extern_extensions().items():
            state_ctx.add_type(extern_name, extern)
        state_args = create_state_args(state_ctx, type_ctx, pipe_val.params)
        p4_state = P4State(pipe_name, state_args)
        p4_state.initialize(state_ctx)
        return state_ctx, p4_state

    def initialize(self, ctx, *args, **kwargs):
        merged_args = merge_parameters(self.params, *args, **kwargs)
        for pipe_name, pipe_arg in merged_args.items():
            log.info("Loading %s pipe...", pipe_name)
            pipe_val = ctx.resolve_expr(pipe_arg.p4_val)
            if isinstance(pipe_val, P4Control):
                # create the z3 representation of this control state
                state_ctx, p4_state = self.build_state_ctx(
                    ctx, pipe_name, pipe_arg, pipe_val)
                state_ctx.set_p4_state(p4_state)
                # initialize the call with its own params we collected
                # this is essentially the input packet
                args = []
                for param in pipe_val.params:
                    args.append(param.name)
                pipe_val.apply(state_ctx, *args)
                # after executing the pipeline get its z3 representation
                z3_function = p4_state.create_z3_representation(state_ctx)
                # all done, that is our P4 representation!
                self.pipes[pipe_name] = (z3_function, p4_state, pipe_val)
            elif isinstance(pipe_val, P4Extern):
                var = z3.Const(f"{pipe_name}{pipe_val.name}", pipe_val.z3_type)
                self.pipes[pipe_name] = (var, None, pipe_val)
            elif isinstance(pipe_val, P4Package):
                # execute the package by calling its initializer
                # pipe_val.initialize(ctx)
                # resolve all the sub_pipes
                for sub_pipe_name, sub_pipe_val in pipe_val.pipes.items():
                    sub_pipe_name = f"{pipe_name}_{sub_pipe_name}"
                    self.pipes[sub_pipe_name] = sub_pipe_val
            elif isinstance(pipe_val, z3.ExprRef):
                # for some reason simple expressions are also possible.
                self.pipes[pipe_name] = (pipe_val, None, pipe_val)
            else:
                raise RuntimeError(
                    f"Unsupported value {pipe_val}, type {type(pipe_val)}."
                    " It does not make sense as a P4 pipeline.")
        return self

    def get_pipes(self):
        return self.pipes
