#include <core.p4>
extern e<T> {
    e();
    T get();
}
parser p1<T>(out T a) {
    T tmp;
    @name("ei") e<T>() ei_0;
    state start {
        tmp = ei_0.get();
        a = tmp;
        transition accept;
    }
}
parser simple(out bit<2> a);
package m(simple n);
m(p1<bit<2>>()) main;
