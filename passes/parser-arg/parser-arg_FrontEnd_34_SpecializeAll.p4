#include <core.p4>
parser Parser();
package Package(Parser p1, Parser p2);
parser Inside() {
    state start {
        transition accept;
    }
}
parser Parser1_0() {
    Inside() p_0;
    state start {
        p_0.apply();
        transition accept;
    }
}
parser Parser2_0() {
    Inside() p_1;
    state start {
        p_1.apply();
        transition accept;
    }
}
Package(Parser1_0(), Parser2_0()) main;
