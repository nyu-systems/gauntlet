/*
Copyright 2017 Cisco Systems, Inc.

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

/*
The TCP option parsing part of this program has been adapted from
testdata/p4_16_samples/spec-ex19.p4 within the repository
https://github.com/p4lang/p4c by Andy Fingerhut
(andy.fingerhut@gmail.com).  That earlier version also appears in
the P4_16 v1.0.0 specification document.

As of 2017-Nov-09, the P4_16 compiler `p4test` in
https://github.com/p4lang/p4c compiles tcp-options-parser.p4 without
any errors, but `p4c-bm2-ss` gives an error that Tcp_option_h is not a
header type.  This is because as of that date the bmv2 back end code
in `p4c-bm2-ss` code does not yet handle header_union.
*/

#include <core.p4>
#include <v1model.p4>


header Tcp_option_end_h {
    bit<8> kind;
}
header Tcp_option_nop_h {
    bit<8> kind;
}

header_union Tcp_option_h {
    Tcp_option_end_h  end;
    Tcp_option_nop_h  nop;
}

// Defines a stack of 10 tcp options
typedef Tcp_option_h[2] Tcp_option_stack;

header Tcp_option_padding_h {
    bit<256> padding;
}

struct headers {
    Tcp_option_end_h end;
    Tcp_option_nop_h nop;
    Tcp_option_padding_h tcp_options_padding;
}



struct metadata {
}



// This sub-parser is intended to be apply'd just after the base
// 20-byte TCP header has been extracted.  It should be called with
// the value of the Data Offset field.  It will fill in the @vec
// argument with a stack of TCP options found, perhaps empty.

// Unless some error is detect earlier (causing this sub-parser to
// transition to the reject state), it will advance exactly to the end
// of the TCP header, leaving the packet 'pointer' at the first byte
// of the TCP payload (if any).  If the packet ends before the full
// TCP header can be consumed, this sub-parser will set
// error.PacketTooShort and transition to reject.

parser Tcp_option_parser(packet_in b,
                         out headers vec,
                         out Tcp_option_padding_h padding)
{
    bit<7> tcp_hdr_bytes_left;

    state start {
        transition next_option;
    }
    state next_option {
        // precondition: tcp_hdr_bytes_left >= 1
        transition select(b.lookahead<bit<8>>()) {
            0: parse_tcp_option_end;
            1: parse_tcp_option_nop;
            default: accept;
        }
    }
    state parse_tcp_option_end {
        b.extract(vec.end);
        // TBD: This code is an example demonstrating why it would be
        // useful to have sizeof(vec.end) instead of having to
        // put in a hard-coded length for each TCP option.
        transition consume_remaining_tcp_hdr_and_accept;
    }
    state consume_remaining_tcp_hdr_and_accept {
        // A more picky sub-parser implementation would verify that
        // all of the remaining bytes are 0, as specified in RFC 793,
        // setting an error and rejecting if not.  This one skips past
        // the rest of the TCP header without checking this.

        // tcp_hdr_bytes_left might be as large as 40, so multiplying
        // it by 8 it may be up to 320, which requires 9 bits to avoid
        // losing any information.
        vec.end.kind = 1;
        transition accept;
    }
    state parse_tcp_option_nop {
        b.extract(vec.nop);
        transition next_option;
    }

}

parser ParserImpl(packet_in packet,
                  out headers hdr,
                  inout metadata meta,
                  inout standard_metadata_t standard_metadata) {

    state start {
        Tcp_option_parser.apply(packet, hdr, hdr.tcp_options_padding);
        transition accept;
    }

}

action my_drop(inout standard_metadata_t smeta) {
    mark_to_drop(smeta);
}

control ingress(inout headers hdr,
                inout metadata meta,
                inout standard_metadata_t standard_metadata) {


    apply {
    }
}

control egress(inout headers hdr,
               inout metadata meta,
               inout standard_metadata_t standard_metadata)
{


    apply {
    }
}

control DeparserImpl(packet_out packet, in headers hdr) {
    apply {
    }
}

control verifyChecksum(inout headers hdr, inout metadata meta) {
    apply {
    }
}

control computeChecksum(inout headers hdr, inout metadata meta) {
    apply {
    }
}

V1Switch(ParserImpl(),
         verifyChecksum(),
         ingress(),
         egress(),
         computeChecksum(),
         DeparserImpl()) main;
