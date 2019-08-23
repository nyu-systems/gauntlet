#include <core.p4>
parser p() {
    state start {
        transition select(8w5, 8w5, 8w5, 8w5, 8w5) {
            (8w0, 8w0, 8w0, 8w0, 8w0): accept;
            (8w1, 8w1, default, default, 8w1): accept;
            default: reject;
        }
    }
}
parser s();
package top(s _s);
top(p()) main;
