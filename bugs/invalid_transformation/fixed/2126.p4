/*
Copyright 2020 Cisco Systems, Inc.

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

header ethernet_t {
    bit<48> dstAddr;
    bit<48> srcAddr;
    bit<16> etherType;
}

struct headers_t {
    ethernet_t ethernet;
}

struct metadata_t {
    bit<16> tmp_port;
}

parser parserImpl(packet_in packet,
                  out headers_t hdr,
                  inout metadata_t meta,
                  inout standard_metadata_t stdmeta)
{
    state start {
        bit<16> tmp_port_0;
        {
            bit<16> retval;
            retval = ((bit<16>) stdmeta.ingress_port) + 1;
            tmp_port_0 = retval;
        }
        packet.extract(hdr.ethernet);
        {
            // With latest p4c as of 2020-Jan-04, the compiler gives
            // an error message "Duplicate declaration of retval" for
            // the next line.  It seems that it should be in a
            // completely separate lexical scope, and the earlier
            // definition should not be in scope at this point, so
            // this should be legal code.

            // Changing the following 3 occurrences of 'retval' to a
            // different name like 'retval2' causes no error message
            // during compilation.
            bit<16> retval;
            retval = hdr.ethernet.etherType + 1;
            hdr.ethernet.etherType = retval;
        }
        meta.tmp_port = tmp_port_0;
        transition accept;
    }
}

control verifyChecksum(inout headers_t hdr, inout metadata_t meta) {
    apply { }
}

control ingressImpl(inout headers_t hdr,
                    inout metadata_t meta,
                    inout standard_metadata_t stdmeta)
{
    apply {
    }
}

control egressImpl(inout headers_t hdr,
                   inout metadata_t meta,
                   inout standard_metadata_t stdmeta)
{
    apply { }
}

control updateChecksum(inout headers_t hdr, inout metadata_t meta) {
    apply { }
}

control deparserImpl(packet_out packet,
                     in headers_t hdr)
{
    apply {
        packet.emit(hdr.ethernet);
    }
}

V1Switch(parserImpl(),
         verifyChecksum(),
         ingressImpl(),
         egressImpl(),
         updateChecksum(),
         deparserImpl()) main;
