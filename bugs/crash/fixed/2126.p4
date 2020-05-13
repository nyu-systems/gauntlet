/*Invoking preprocessor
cpp -C -undef -nostdinc -x assembler-with-cpp  -Ip4_tv/p4c/build/p4include -D__TARGET_BMV2__ -Ip4_tv/p4c/build/p4include -Ip4_tv/p4c/build/p4include ./2126.p4i
bugs/crash/fixed/2126.p4(58): error: Duplicate declaration of retval; previous at
            bit<16> retval;
                    ^^^^^^
bugs/crash/fixed/2126.p4(42)
            bit<16> retval;
                    ^^^^^^
error: 1 errors encountered, aborting compilation
running cc -E -C -undef -nostdinc -x assembler-with-cpp -I p4_tv/p4c/build/p4include -o ./2126.p4i bugs/crash/fixed/2126.p4
running p4_tv/p4c/build/p4c-bm2-ss -I p4_tv/p4c/build/p4include --p4v=16 -vvv -o ./2126.json ./2126.p4i --arch v1model
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
