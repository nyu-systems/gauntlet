#include <core.p4>
#include <v1model.p4>
parser p() {
    state start {
        bit<32> x_0;
        transition select(x_0) {
            32w0: reject;
        }
    }
}
parser e();
package top(e e);
top(p()) main;
