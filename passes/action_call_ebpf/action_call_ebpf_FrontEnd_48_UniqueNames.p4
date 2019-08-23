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
    bool x;
    @name("Reject") action Reject(bool rej_0) {
        pass = rej_0;
    }
    apply {
        x = true;
        Reject(x);
    }
}
ebpfFilter<Headers_t>(prs(), pipe()) main;
