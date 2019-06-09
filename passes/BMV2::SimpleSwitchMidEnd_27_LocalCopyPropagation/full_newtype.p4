#include <core.p4>
typedef bit<32> B32;
typedef bit<32> N32;
struct S {
    B32 b;
    N32 n;
}
header H {
    N32 field;
}
control c(out B32 x) {
    N32 k_0;
    @name(".NoAction") action NoAction_0() {
    }
    @name("c.t") table t_0 {
        actions = {
            NoAction_0();
        }
        key = {
            k_0: exact @name("k") ;
        }
        default_action = NoAction_0();
    }
    apply {
        k_0 = 32w0;
        x = (B32)32w0;
        if (32w0 == 32w1) 
            x = 32w2;
        t_0.apply();
        if (32w0 == (B32)32w0) 
            x = 32w3;
    }
}
control e(out B32 x);
package top(e _e);
top(c()) main;
