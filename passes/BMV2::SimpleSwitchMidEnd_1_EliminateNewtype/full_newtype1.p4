typedef bit<9> Narrow_t;
typedef Narrow_t Narrow;
typedef bit<32> Wide_t;
typedef Wide_t Wide;
control c(out bool b) {
    Wide x;
    Narrow y;
    apply {
        x = 32w3;
        y = (Narrow_t)(Wide_t)x;
        b = y == 9w10;
    }
}
control ctrl(out bool b);
package top(ctrl _c);
top(c()) main;
