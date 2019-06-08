control ctrl() {
    apply {
        exit;
    }
}
control noop();
package p(noop _n);
p(ctrl()) main;
