control d(out bit<32> x) {
    @name("cinst.a1") action cinst_a1_0() {
    }
    @name("cinst.a2") action cinst_a2_0() {
    }
    @name("cinst.t") table cinst_t_0 {
        actions = {
            cinst_a1_0();
            cinst_a2_0();
        }
        default_action = cinst_a1_0();
    }
    apply {
        {
            bool cinst_hasReturned_0 = false;
            switch (cinst_t_0.apply().action_run) {
                cinst_a1_0: 
                cinst_a2_0: {
                    cinst_hasReturned_0 = true;
                }
                default: {
                    cinst_hasReturned_0 = true;
                }
            }
        }
    }
}
control dproto(out bit<32> x);
package top(dproto _d);
top(d()) main;
