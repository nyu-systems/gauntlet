#include <core.p4>
extern Virtual {
    Virtual();
    void increment();
    @synchronous(increment) abstract bit<16> f(in bit<16> ix);
    bit<16> total();
}
control c(inout bit<16> p) {
    bit<16> local_0;
    @name("cntr") Virtual() cntr_0 = {
        bit<16> f(in bit<16> ix) {
            return ix + local_0;
        }
    };
    @name("final_ctr") action final_ctr_0() {
        bit<16> tmp;
        {
            tmp = cntr_0.total();
            p = tmp;
        }
    }
    @name("add_ctr") action add_ctr_0() {
        {
            cntr_0.increment();
        }
    }
    @name("run_ctr") table run_ctr_0 {
        key = {
            p: exact @name("p") ;
        }
        actions = {
            add_ctr_0();
            final_ctr_0();
            @defaultonly NoAction();
        }
        default_action = NoAction();
    }
    apply {
        {
            local_0 = 16w4;
        }
        {
            run_ctr_0.apply();
        }
    }
}
control ctr(inout bit<16> x);
package top(ctr ctrl);
top(c()) main;
