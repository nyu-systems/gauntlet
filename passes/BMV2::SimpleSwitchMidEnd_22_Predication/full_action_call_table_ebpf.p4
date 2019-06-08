#include <core.p4>
#include <ebpf_model.p4>
struct Headers_t {
}
parser prs(packet_in p, out Headers_t headers) {
    state start {
        transition accept;
    }
}
control pipe(inout Headers_t headers, out bool pass) {
    @name("pipe.Reject") action Reject_0(bit<8> rej, bit<8> bar) {
        {
            bool cond;
            {
                bool pred;
                cond = rej == 8w0;
                pred = cond;
                pass = (pred ? true : pass);
                cond = !cond;
                pred = cond;
                pass = (pred ? false : pass);
            }
        }
        {
            bool cond_0;
            {
                bool pred_0;
                cond_0 = bar == 8w0;
                pred_0 = cond_0;
                pass = (pred_0 ? false : pass);
            }
        }
    }
    @name("pipe.t") table t {
        actions = {
            Reject_0();
        }
        default_action = Reject_0(8w1, 8w0);
    }
    apply {
        t.apply();
    }
}
ebpfFilter<Headers_t>(prs(), pipe()) main;
