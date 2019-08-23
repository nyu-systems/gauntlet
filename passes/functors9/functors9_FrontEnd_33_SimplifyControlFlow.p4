#include <core.p4>
extern e<T> {
    e();
    T get();
}
parser p1<T>(in T a) {
    T w_0;
    T tmp;
    @name("ei") e<T>() ei_0;
    state start {
        tmp = ei_0.get();
        transition accept;
    }
}
parser simple(in bit<2> a);
package m(simple n);
m(p1<bit<2>>()) main;
