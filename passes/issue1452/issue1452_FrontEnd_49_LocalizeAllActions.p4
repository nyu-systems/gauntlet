control c() {
    bit<32> x;
    @name("a") action a_0(inout bit<32> arg_0) {
        bool hasReturned_0 = false;
        arg_0 = 32w1;
        hasReturned_0 = true;
    }
    apply {
        a_0(x);
    }
}
control proto();
package top(proto p);
top(c()) main;
