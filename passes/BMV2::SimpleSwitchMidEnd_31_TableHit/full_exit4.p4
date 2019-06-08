control ctrl() {
    bool tmp_0;
    @name("ctrl.e") action e_0() {
        exit;
    }
    @name("ctrl.t") table t {
        actions = {
            e_0();
        }
        default_action = e_0();
    }
    apply {
        if (t.apply().hit) 
            tmp_0 = true;
        else 
            tmp_0 = false;
        if (tmp_0) 
            t.apply();
        else 
            t.apply();
    }
}
control noop();
package p(noop _n);
p(ctrl()) main;
