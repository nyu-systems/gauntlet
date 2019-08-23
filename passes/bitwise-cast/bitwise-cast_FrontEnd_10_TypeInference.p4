#include <core.p4>
control p() {
    apply {
        bit<1> a;
        bit<8> b = (bit<8>)8w3;
        bit<8> c = (bit<8>)8w4;
        a = (bit<1>)(b == 8w1) & (bit<1>)(c == 8w2);
    }
}
