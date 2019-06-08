#include <core.p4>
extern Fake {
    Fake();
    void call(in bit<32> data);
}
parser P() {
    bit<32> x;
    @name("P.fake") Fake() fake;
    state start {
        x = 32w0;
        fake.call(x);
        transition accept;
    }
}
control C() {
    @name("C.fake") Fake() fake_2;
    apply {
        fake_2.call(32w0 + 32w1);
    }
}
parser SimpleParser();
control SimpleControl();
package top(SimpleParser prs, SimpleControl ctrl);
top(P(), C()) main;
