#include <core.p4>
extern e<T> {
    e();
    T get();
}
parser p1<T>(in T a) {
    @name("ei") e<T>() ei_0;
    state start {
        T w_0 = ei_0.get();
        transition accept;
    }
}
parser simple(in bit<2> a);
package m(simple n);
m(p1<bit<2>>()) main;
