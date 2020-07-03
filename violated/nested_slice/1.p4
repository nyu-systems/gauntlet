/*
Copyright 2013-present Barefoot Networks, Inc.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
*/

#include <core.p4>
#include <v1model.p4>

// This program processes packets composed of an Ethernet and
// an IPv4 header, performing forwarding based on the
// destination IP address

// standard Ethernet header
header H {
    bit<8> a;
    bit<8> b;
    bit<8> c;
}

// Parser section

// List of all recognized headers
struct Headers {
    H h ;
}

struct Metadata {
}

parser P(packet_in b,
         out Headers p,
         inout Metadata meta,
         inout standard_metadata_t standard_meta) {
    state start {
        transition accept;
    }
}

// match-action pipeline section

control Ing(inout Headers headers,
            inout Metadata meta,
            inout standard_metadata_t standard_meta) {

    apply {
        bit<8> n = 8w0b11111111;
        bit<8> m = 8w0b11111111;
        bit<8> x = 8w0b11111111;
        n[7:3][4:2][2:0] = 3w2;
        m[7:4][3:1] = 3w0;
        x[5:4][1:1] = 1w0;
        headers.h.a = n;
        headers.h.b = m;
        headers.h.c = x;
    }
}

control Eg(inout Headers hdrs,
               inout Metadata meta,
               inout standard_metadata_t standard_meta) {

    apply {
    }
}

// deparser section
control DP(packet_out b, in Headers p) {
    apply {
    }
}

// Fillers
control Verify(inout Headers hdrs, inout Metadata meta) {
    apply {}
}

control Compute(inout Headers hdr, inout Metadata meta) {
    apply {}
}

// Instantiate the top-level V1 Model package.
V1Switch(P(),
         Verify(),
         Ing(),
         Eg(),
         Compute(),
         DP()) main;
