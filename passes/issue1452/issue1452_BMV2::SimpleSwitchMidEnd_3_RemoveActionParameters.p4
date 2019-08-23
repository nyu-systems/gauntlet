control c() {
    bit<32> x_0;
    bool hasReturned;
    bit<32> arg;
    @name("c.a") action a() {
        arg = x_0;
        hasReturned = false;
        arg = 32w1;
        hasReturned = true;
        x_0 = arg;
    }
    apply {
        a();
    }
}
control proto();
package top(proto p);
top(c()) main;
