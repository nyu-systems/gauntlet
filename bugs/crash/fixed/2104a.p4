#include <core.p4>
#include <v1model.p4>

control c() {
    bit<16> FHaSkb = 0;
    bit<128> YIafjU = 0;
    action rxNET() {
        YIafjU = (bit<128>) FHaSkb;

    }
    action vKNsz() {
        return; // the return comes before the action call
        rxNET();
    }
    apply {
        vKNsz();
    }

}

control e<T>();
package top<T>(e<T> e);

top(c()) main;
