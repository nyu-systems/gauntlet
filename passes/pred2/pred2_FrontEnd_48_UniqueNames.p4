#include <core.p4>
#include <v1model.p4>
control empty();
package top(empty e);
control Ing() {
    bool tmp_0;
    @name("cond") action cond_0() {
        tmp_0 = tmp_0;
    }
    @name("tbl_cond") table tbl_cond {
        actions = {
            cond_0();
        }
        const default_action = cond_0();
    }
    apply {
        tbl_cond.apply();
    }
}
top(Ing()) main;
