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

#include <core.p4>
#include <v1model.p4>


typedef bit<48>  EthernetAddress;

header ethernet_t {
    bit<16> dstAddr_hi;
    bit<32> dstAddr_lo;
    bit<16> srcAddr_hi;
    bit<32> srcAddr_lo;
    bit<16>         etherType;
}

struct metadata {
}

struct headers {
    ethernet_t       ethernet;
}


parser IngressParserImpl(packet_in buffer,
                         out headers hdr,
                         inout metadata user_meta,
                         inout standard_metadata_t standard_metadata)
{
    state start {
        buffer.extract(hdr.ethernet);
        transition accept;
    }
}

control ingress(inout headers hdr,
                inout metadata user_meta,
                inout standard_metadata_t standard_metadata) {
    bit<16> tmp;
    bit<32> x1;
    bit<16> x2;
    apply {
        hdr.ethernet.dstAddr_hi = 0;
        hdr.ethernet.dstAddr_lo = (bit<32>) (~hdr.ethernet.etherType);
        hdr.ethernet.srcAddr_hi = 0;
        hdr.ethernet.srcAddr_lo = ~((bit<32>) hdr.ethernet.etherType);
    }
}

control egress(inout headers hdr,
               inout metadata user_meta,
               inout standard_metadata_t standard_metadata)
{
    apply { }
}

control DeparserImpl(packet_out packet, in headers hdr) {
    apply {
        packet.emit(hdr.ethernet);
    }
}

control verifyChecksum(inout headers hdr, inout metadata meta) {
    apply { }
}

control computeChecksum(inout headers hdr, inout metadata meta) {
    apply { }
}

V1Switch(IngressParserImpl(),
         verifyChecksum(),
         ingress(),
         egress(),
         computeChecksum(),
         DeparserImpl()) main;
