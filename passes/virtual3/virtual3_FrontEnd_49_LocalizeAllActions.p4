#include <core.p4>
extern Virtual {
    Virtual();
    void increment();
    @synchronous(increment) abstract bit<16> f(in bit<16> ix);
    bit<16> total();
}
control c(inout bit<16> p) {
    @name(".NoAction") action NoAction_1() {
    }
    bit<16> local;
    bit<16> tmp_0;
    @name("cntr") Virtual() cntr = {
        bit<16> f(in bit<16> ix) {
            return ix + local;
        }
    };
    @name("final_ctr") action final_ctr_0() {
        tmp_0 = cntr.total();
        p = tmp_0;
    }
    @name("add_ctr") action add_ctr_0() {
        cntr.increment();
    }
    @name("run_ctr") table run_ctr {
        key = {
            p: exact @name("p") ;
        }
        actions = {
            add_ctr_0();
            final_ctr_0();
            @defaultonly NoAction_1();
        }
        default_action = NoAction_1();
    }
    apply {
        local = 16w4;
        run_ctr.apply();
    }
}
control ctr(inout bit<16> x);
package top(ctr ctrl);
top(c()) main;
