#include <core.p4>
extern Fake {
    Fake();
    void call(in bit<32> data);
}
parser P() {
    bit<32> x_0 = 32w0;
    @name("fake") Fake() fake_0;
    state start {
        fake_0.call(x_0);
        transition accept;
    }
}
control C() {
    bit<32> x_1 = 32w0;
    bit<32> y_0 = x_1 + 32w1;
    @name("fake") Fake() fake_1;
    apply {
        fake_1.call(y_0);
    }
}
parser SimpleParser();
control SimpleControl();
package top(SimpleParser prs, SimpleControl ctrl);
top(P(), C()) main;
