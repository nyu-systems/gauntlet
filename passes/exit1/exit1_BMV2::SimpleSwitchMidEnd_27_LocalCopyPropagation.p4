control ctrl() {
    apply {
        if (32w0 == 32w0) {
            exit;
        } else {
            exit;
        }
    }
}
control noop();
package p(noop _n);
p(ctrl()) main;
